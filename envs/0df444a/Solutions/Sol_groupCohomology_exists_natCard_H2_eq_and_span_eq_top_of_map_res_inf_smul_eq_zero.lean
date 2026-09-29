-- Prove2me | solution 1 for groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/39a3521c-a809-5408-b57e-2ee0a8e5beef

import Mathlib
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

theorem solution
    {k Γ : Type} [CommRing k] [Group Γ] [Fintype Γ] (C : Rep k Γ) (S T : Subgroup Γ) [S.Normal] [T.Normal]
    [Fintype (Γ ⧸ S)]
    (hS1 : IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hT1 : IsZero (groupCohomology (Rep.res T.subtype C) 1))
    (n' : ℕ) (hn : Fintype.card (Γ ⧸ S) ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology (C.quotientToInvariants T) 2) (hu' : addOrderOf u' = n')
    (hres : (map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom
        ((n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u') = 0)
    (hfin : Finite (groupCohomology (C.quotientToInvariants S) 2))
    (hle : Nat.card (groupCohomology (C.quotientToInvariants S) 2) ≤ Fintype.card (Γ ⧸ S)) :
    ∃ y : groupCohomology (C.quotientToInvariants S) 2,
      Nat.card (groupCohomology (C.quotientToInvariants S) 2) = Fintype.card (Γ ⧸ S) ∧
      Submodule.span k {y} = ⊤ ∧
      (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
          (ofHom (C.ρ.quotientToInvariants_lift S)) 2).hom y =
        (n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u' := by
  classical

  obtain ⟨hinjT, -⟩ := groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 C T hT1
  obtain ⟨hinjS, hrangeS⟩ := groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 C S hS1
  set infT := ModuleCat.Hom.hom (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
      (ofHom (C.ρ.quotientToInvariants_lift T)) 2) with hinfT
  set infS := ModuleCat.Hom.hom (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
      (ofHom (C.ρ.quotientToInvariants_lift S)) 2) with hinfS
  set n := Fintype.card (Γ ⧸ S) with hn_def
  have hn0 : n ≠ 0 := Fintype.card_ne_zero
  set x := (n' / n) • infT u' with hx

  have hordw : addOrderOf (infT u') = n' := by rw [← hu']; exact addOrderOf_injective infT.toAddMonoidHom hinjT u'
  have hm0 : n' / n ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hn).mpr ⟨hn'0, hn0⟩
  have hordx : addOrderOf x = n := by
    rw [hx, addOrderOf_nsmul' _ hm0, hordw, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hn), Nat.div_div_self hn hn'0]

  have hxker : x ∈ LinearMap.ker (ModuleCat.Hom.hom (map S.subtype (𝟙 (Rep.res S.subtype C)) 2)) := by
    rw [LinearMap.mem_ker]; exact hres
  rw [← hrangeS] at hxker
  obtain ⟨y, hy⟩ := hxker
  have hordy : addOrderOf y = n := by
    have h1 : addOrderOf (infS y) = addOrderOf y := addOrderOf_injective infS.toAddMonoidHom hinjS y
    rw [← h1]; show addOrderOf (infS y) = n; rw [hy, hordx]

  haveI := hfin
  letI : Fintype (groupCohomology (C.quotientToInvariants S) 2) := Fintype.ofFinite _
  have hcard : Nat.card (groupCohomology (C.quotientToInvariants S) 2) = n := by
    refine le_antisymm hle ?_
    calc n = addOrderOf y := hordy.symm
      _ ≤ Fintype.card (groupCohomology (C.quotientToInvariants S) 2) := addOrderOf_le_card_univ
      _ = Nat.card (groupCohomology (C.quotientToInvariants S) 2) := (Nat.card_eq_fintype_card).symm
  have hzm : AddSubgroup.zmultiples y = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hordy, hcard]
  refine ⟨y, hcard, ?_, hy⟩
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ AddSubgroup.zmultiples y := by rw [hzm]; trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  rw [← hm, ← Int.cast_smul_eq_zsmul k m y]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

end S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero
end P2MW
export P2MW.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero (solution)
