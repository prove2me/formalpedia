-- Prove2me | solution 1 for exists_isMaximalDisjoint_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:52.198801+00:00
-- url     : https://prove2.me/submissions/7941b21b-8768-43ed-9b6e-5795bbb12448

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
theorem _root_.solution (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] :
    ∃ Λ : Set X, IsMaximalDisjoint Λ ∧ ∀ x ∈ Λ, 0 < x := by
  let 𝒞 : Set (Set X) := {S | IsDisjointSet S ∧ ∀ x ∈ S, 0 < x}
  have hZorn : ∀ c ⊆ 𝒞, IsChain (· ⊆ ·) c → ∃ ub ∈ 𝒞, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro ⟨S, hS, h0⟩
      exact (hc hS).1.1 h0
    · intro a ha b hb hab
      obtain ⟨Sa, hSa, haSa⟩ := ha
      obtain ⟨Sb, hSb, hbSb⟩ := hb
      rcases hchain.total hSa hSb with hSab | hSab
      · exact (hc hSb).1.2 (hSab haSa) hbSb hab
      · exact (hc hSa).1.2 haSa (hSab hbSb) hab
    · rintro x ⟨S, hS, hxS⟩
      exact (hc hS).2 x hxS
  obtain ⟨Λ, hΛ⟩ := zorn_subset 𝒞 hZorn
  refine ⟨Λ, ⟨hΛ.prop.1, ?_⟩, hΛ.prop.2⟩
  intro Λ' hΛ' hsub y hy
  by_contra hyΛ
  have hyΛ : y ∉ Λ := hyΛ
  have hy_ne : y ≠ 0 := fun h => hΛ'.1 (h ▸ hy)
  have habsy_ne : |y| ≠ 0 := fun h => hy_ne ((abs_eq_zero_iff_zero y).mp h)
  have habsy_pos : 0 < |y| := lt_of_le_of_ne (abs_nonneg y) (Ne.symm habsy_ne)
  have hy_disj : ∀ a ∈ Λ, IsVLDisjoint y a := by
    intro a ha
    have hane : y ≠ a := fun h => hyΛ (h.symm ▸ ha)
    exact hΛ'.2 hy (hsub ha) hane
  set Λ'' : Set X := insert |y| Λ
  have hΛ''_in : Λ'' ∈ 𝒞 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro (h0 | h0)
      · exact habsy_ne h0.symm
      · exact hΛ.prop.1.1 h0
    · intro a ha b hb hab
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hab rfl).elim
        · exact (hy_disj b hb).mono_left (abs_of_nonneg (abs_nonneg y)).le
      · rcases hb with rfl | hb
        · exact isVLDisjoint_comm.mp
            ((hy_disj a ha).mono_left (abs_of_nonneg (abs_nonneg y)).le)
        · exact hΛ.prop.1.2 ha hb hab
    · rintro x (rfl | hx)
      · exact habsy_pos
      · exact hΛ.prop.2 x hx
  have hsub'' : Λ ⊆ Λ'' := Set.subset_insert _ _
  have hsub''' : Λ'' ⊆ Λ := hΛ.2 hΛ''_in hsub''
  have habs_in : |y| ∈ Λ := hsub''' (Set.mem_insert _ _)
  by_cases hyabs : y = |y|
  · exact hyΛ (hyabs ▸ habs_in)
  · have hd : |y| ⊓ |(|y|)| = 0 := hΛ'.2 hy (hsub habs_in) hyabs
    rw [abs_of_nonneg (abs_nonneg y), inf_idem] at hd
    exact habsy_ne hd
