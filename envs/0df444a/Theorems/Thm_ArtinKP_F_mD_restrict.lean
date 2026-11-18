-- Prove2me | Theorems.Thm_ArtinKP_F_mD_restrict
-- name    : ArtinKP.F.mD_restrict
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:40.416162+00:00
-- url     : https://prove2.me/theorems/740a5b7e-faf0-44ec-8270-c709d4773ccd
-- title:
--   ArtinKP.F.mD_restrict: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.F`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem mD_restrict (Φ₁ : GSection ι P 𝔪) {Γ' : Subgroup (SL(2, 𝓞 F))} [Γ'.FiniteIndex]
--       (hΓ₁ : Inv Γ' (Φ₁.twist hG hz6))
--       (hΓR : Inv Γ' (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)))
--       {D₁ : Set (InfinitePlace F → ℂ)} (hD₁ : PCell (latN Γ') D₁) {n₁ : ℕ}
--       (hb₁ : ∀ x ∈ D₁, ∀ w, ‖x w‖ ≤ n₁) {s : ℂ} (hs : 2 < s.re) :
--       mD D₁ (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)) s
--         = ratio (Ideal.absNorm v.asIdeal : ℂ) s * mD D₁ (Φ₁.twist hG hz6) s
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.FA.not_le_of_good` and `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.C5.Inv`, `ArtinKP.N.latN` and `ArtinKP.T.PCell` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.F.ratio`, `ArtinKP.N.mD` and `ArtinKP.S.TSection.restrict` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.F.zPsi_restrict_twist` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

include hG hz6 h g in
theorem mD_restrict (Φ₁ : GSection ι P 𝔪) {Γ' : Subgroup (SL(2, 𝓞 F))} [Γ'.FiniteIndex]
    (hΓ₁ : Inv Γ' (Φ₁.twist hG hz6))
    (hΓR : Inv Γ' (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)))
    {D₁ : Set (InfinitePlace F → ℂ)} (hD₁ : PCell (latN Γ') D₁) {n₁ : ℕ}
    (hb₁ : ∀ x ∈ D₁, ∀ w, ‖x w‖ ≤ n₁) {s : ℂ} (hs : 2 < s.re) :
    mD D₁ (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)) s
      = ratio (Ideal.absNorm v.asIdeal : ℂ) s * mD D₁ (Φ₁.twist hG hz6) s := by
  sorry

end gen

end

end ArtinKP.F
end
