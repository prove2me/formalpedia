-- Prove2me | solution 1 for groupCohomology.restriction_injective_of_index_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:47.334445+00:00
-- url     : https://prove2.me/submissions/ffc0a2de-a4ba-4aee-8efd-9a577d460ea9

import Mathlib
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

local instance instL_groupCohomology_restriction_injective_of_23397f_s27a302 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Restriction to an index-five subgroup is injective on mod-71 cohomology.
The corestriction identity is used with the identity coefficient map. -/
theorem _root_.solution
    {G : Type} [Group G] (S : Subgroup G) [S.FiniteIndex]
    (hindex : S.index = 5) (M : Rep (ZMod 71) G) (n : ℕ) :
    Function.Injective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n).hom := by
  classical
  letI : Fintype (G ⧸ S) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ S) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact hindex
  obtain ⟨cor, hcor⟩ := exists_corestriction_map_map_res_eq_map_norm S M n
  have hnorm (x : M) : (5 • (𝟙 M)).hom x =
      ∑ g : G ⧸ S, M.ρ g.out (M.ρ g.out⁻¹ x) := by
    change 5 • x = ∑ g : G ⧸ S, M.ρ g.out (M.ρ g.out⁻¹ x)
    simp_rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
    simp [hcard]
  have hmap (z : groupCohomology M n) :
      (groupCohomology.map (MonoidHom.id G) (5 • (𝟙 M)) n).hom z = 5 • z := by
    induction z using groupCohomology_induction_on with
    | h c =>
      rw [groupCohomology.π_map_apply, ← map_nsmul]
      congr 1
      apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles M n)).1 inferInstance
      rw [map_nsmul]
      change ((groupCohomology.cocyclesMap (MonoidHom.id G) (5 • (𝟙 M)) n ≫
        groupCohomology.iCocycles M n).hom c) = _
      rw [HomologicalComplex.cyclesMap_i]
      refine groupCohomology.inhomogeneousCochains.ext fun g => ?_
      rfl
  intro x y hxy
  have hx := hcor M (𝟙 (Rep.res S.subtype M)) (5 • (𝟙 M)) hnorm x
  have hy := hcor M (𝟙 (Rep.res S.subtype M)) (5 • (𝟙 M)) hnorm y
  rw [groupCohomology.map_id, hmap] at hx hy
  have heq : 5 • x = 5 • y := hx.symm.trans ((congrArg cor hxy).trans hy)
  have hsmul : (5 : ZMod 71) • x = (5 : ZMod 71) • y := by
    change ((5 : ℕ) : ZMod 71) • x = ((5 : ℕ) : ZMod 71) • y
    simpa only [Nat.cast_smul_eq_nsmul] using heq
  have hinv := congrArg (fun z : groupCohomology M n => (5 : ZMod 71)⁻¹ • z) hsmul
  simpa only [smul_smul, inv_mul_cancel₀ (by decide : (5 : ZMod 71) ≠ 0),
    one_smul] using hinv

end groupCohomology
