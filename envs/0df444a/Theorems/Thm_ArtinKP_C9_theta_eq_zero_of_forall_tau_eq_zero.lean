-- Prove2me | Theorems.Thm_ArtinKP_C9_theta_eq_zero_of_forall_tau_eq_zero
-- name    : ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:50.25504+00:00
-- url     : https://prove2.me/theorems/d061f7a5-2141-4850-b372-06dee3d7f13e
-- title:
--   ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.C9`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem theta_eq_zero_of_forall_tau_eq_zero (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
--       (hΓ : Inv Γ (Φ.twist hG hz6)) (hdual : DualCover 𝔪 Γ)
--       (h : ∀ ν : SInt 𝔪, ν ≠ 0 → T.tau hG hz6 Φ ν = 0) :
--       C5.theta Γ (Φ.twist hG hz6) = 0
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.C5.Inv`, `ArtinKP.C5.theta` and `ArtinKP.T.tau` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.C9.DualCover` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.GK.kw_theta_of_diffInS` of this split imports it.
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

attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

section tau

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

theorem theta_eq_zero_of_forall_tau_eq_zero (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) (hdual : DualCover 𝔪 Γ)
    (h : ∀ ν : SInt 𝔪, ν ≠ 0 → T.tau hG hz6 Φ ν = 0) :
    C5.theta Γ (Φ.twist hG hz6) = 0 := by
  sorry

end tau

end

end ArtinKP.C9
end
