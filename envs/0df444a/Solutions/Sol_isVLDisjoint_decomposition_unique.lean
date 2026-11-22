-- Prove2me | solution 1 for isVLDisjoint_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:19.980641+00:00
-- url     : https://prove2.me/submissions/80c9d246-7b42-4905-9a8a-e8b78d1a1141

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_inf_eq_zero_of_isVLDisjoint
public import Theorems.Thm_uniqueness_posPart


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {u₁ v₁ u₂ v₂ : X}
    (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁) (hu₂ : 0 ≤ u₂) (hv₂ : 0 ≤ v₂)
    (hd₁ : IsVLDisjoint u₁ v₁) (hd₂ : IsVLDisjoint u₂ v₂)
    (h : u₁ - v₁ = u₂ - v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  have h1 := inf_eq_zero_of_isVLDisjoint hu₁ hv₁ hd₁
  have h2 := inf_eq_zero_of_isVLDisjoint hu₂ hv₂ hd₂
  have eq1 : u₁ = (u₁ - v₁)⁺ :=
    uniqueness_posPart (u₁ - v₁) rfl h1
  have eq2 : u₂ = (u₂ - v₂)⁺ :=
    uniqueness_posPart (u₂ - v₂) rfl h2
  have hu : u₁ = u₂ := by rw [eq1, h, ← eq2]
  refine ⟨hu, ?_⟩
  have := h; rw [hu, sub_eq_add_neg, sub_eq_add_neg] at this
  exact neg_injective (add_left_cancel this)
