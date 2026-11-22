-- Prove2me | solution 1 for isMaximalDisjoint_iff_forall_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:50.87846+00:00
-- url     : https://prove2.me/submissions/8843c1c9-2aaa-4387-8f80-95f4c9ed75ba

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_comm
public import Theorems.Thm_IsVLDisjoint_mono_left
public import Theorems.Thm_abs_eq_zero_iff_zero


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [VectorLattice X]
theorem _root_.solution {Λ : Set X}
    (hdis : IsDisjointSet Λ) :
    IsMaximalDisjoint Λ ↔ ∀ x : X, (∀ a ∈ Λ, IsVLDisjoint x a) → x = 0 := by
  refine ⟨?_, ?_⟩
  · intro hmax x hx
    by_contra hxne
    have habs_ne : |x| ≠ 0 := fun h => hxne ((abs_eq_zero_iff_zero x).mp h)
    have habs_pos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm habs_ne)
    have habs_disj : ∀ a ∈ Λ, IsVLDisjoint |x| a := fun a ha =>
      (hx a ha).mono_left (abs_of_nonneg (abs_nonneg x)).le
    set Λ' : Set X := insert |x| Λ with hΛ'_def
    have hΛ'_dis : IsDisjointSet Λ' := by
      refine ⟨?_, ?_⟩
      · rintro (h0 | h0)
        · exact habs_ne h0.symm
        · exact hdis.1 h0
      · intro a ha b hb hab
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact (hab rfl).elim
          · exact habs_disj b hb
        · rcases hb with rfl | hb
          · exact isVLDisjoint_comm.mp (habs_disj a ha)
          · exact hdis.2 ha hb hab
    have hsub : Λ ⊆ Λ' := Set.subset_insert _ _
    have hsub' : Λ' ⊆ Λ := hmax.2 hΛ'_dis hsub
    have hxinΛ : |x| ∈ Λ := hsub' (Set.mem_insert _ _)
    have hself : |x| ⊓ |(|x|)| = 0 := hx |x| hxinΛ
    rw [abs_of_nonneg (abs_nonneg x), inf_idem] at hself
    exact habs_ne hself
  · intro hyp
    refine ⟨hdis, ?_⟩
    intro Λ' hΛ' hsub y hy
    by_contra hyΛ
    have hyΛ : y ∉ Λ := hyΛ
    have hy_disj : ∀ a ∈ Λ, IsVLDisjoint y a := by
      intro a ha
      have hane : y ≠ a := fun h => hyΛ (h.symm ▸ ha)
      exact hΛ'.2 hy (hsub ha) hane
    have hy0 : y = 0 := hyp y hy_disj
    exact hΛ'.1 (hy0 ▸ hy)
