-- Prove2me | Theorems.Thm_ArtinKP_N2_theta_eq_zero_iff_forall_zPsi_translate_eq_zero
-- name    : ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:11:50.139119+00:00
-- url     : https://prove2.me/theorems/6eae2d08-2081-462d-8fe8-c601dc499d6e
-- title:
--   ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.N2`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem theta_eq_zero_iff_forall_zPsi_translate_eq_zero (hΓ : Inv Γ Ψ) :
--       theta Γ Ψ = 0 ↔ ∀ σ : SL(2, SInt 𝔪), zPsi Pk hG hz6 (TSection.translate Pk hG hz6 σ Ψ) = 0
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.TSection` and `ArtinKP.S.TSection.translate` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.C5.Inv` and `ArtinKP.C5.theta` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.N2.zPsi` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.GK.kw_theta_of_diffInS` and `ArtinKP.GK.theta_per_gen_of_isExterior` of this split import it.
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
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

section

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}

theorem theta_eq_zero_iff_forall_zPsi_translate_eq_zero (hΓ : Inv Γ Ψ) :
    theta Γ Ψ = 0 ↔ ∀ σ : SL(2, SInt 𝔪), zPsi Pk hG hz6 (TSection.translate Pk hG hz6 σ Ψ) = 0 := by
  sorry

end

end

end ArtinKP.N2
end
