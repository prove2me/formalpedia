-- Prove2me | Theorems.Thm_ArtinKP_N2_cusp_integral_eq_zero
-- name    : ArtinKP.N2.cusp_integral_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:57.605163+00:00
-- url     : https://prove2.me/theorems/c235dd04-c85e-4dfa-a142-40b48e62773b
-- title:
--   ArtinKP.N2.cusp_integral_eq_zero: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.N2`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem cusp_integral_eq_zero (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
--       (hz6 : IsPrimitiveRoot z6 6) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
--       {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (σ : SL(2, SInt 𝔪))
--       (hv : CuspVanish Pk hG hz6 Γ Ψ σ) {c : ℝ → ℂ} (hc : Measurable c) (hc1 : ∀ t, ‖c t‖ ≤ 1)
--       {ηK : X F → ℝ≥0∞} (hηK : IsPOU (stab Γ (RO.rowClass hG.ne_bot (Row.bot σ))) ηK)
--       (hfin : ∫⁻ P, ‖c (X.ht (toF 𝔪 σ • P))‖ₑ * ‖X.lift Γ (theta Γ Ψ) P‖ₑ * ηK P ∂X.vol F ≠ ⊤) :
--       ∫ P, c (X.ht (toF 𝔪 σ • P)) * X.lift Γ (theta Γ Ψ) P * (((ηK P).toReal : ℝ) : ℂ)
--         ∂X.vol F = 0
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg`, `ArtinKP.A.Good` and `ArtinKP.A.toF` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.RO.SOf`, `ArtinKP.S.TSection` and `ArtinKP.S.Row.bot` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.IsPOU` (definitions bundle `ArtinKPB008` of this split); `ArtinKP.X.X.lift` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.C5.Inv`, `ArtinKP.C5.theta`, `ArtinKP.RO.rowClass` and `ArtinKP.X.X.ht` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.N.CuspVanish` and `ArtinKP.N2.stab` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.N2.orbit_integral_eq_zero` of this split imports it.
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

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

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

theorem cusp_integral_eq_zero (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (σ : SL(2, SInt 𝔪))
    (hv : CuspVanish Pk hG hz6 Γ Ψ σ) {c : ℝ → ℂ} (hc : Measurable c) (hc1 : ∀ t, ‖c t‖ ≤ 1)
    {ηK : X F → ℝ≥0∞} (hηK : IsPOU (stab Γ (RO.rowClass hG.ne_bot (Row.bot σ))) ηK)
    (hfin : ∫⁻ P, ‖c (X.ht (toF 𝔪 σ • P))‖ₑ * ‖X.lift Γ (theta Γ Ψ) P‖ₑ * ηK P ∂X.vol F ≠ ⊤) :
    ∫ P, c (X.ht (toF 𝔪 σ • P)) * X.lift Γ (theta Γ Ψ) P * (((ηK P).toReal : ℝ) : ℂ)
      ∂X.vol F = 0 := by
  sorry

end

end ArtinKP.N2
end
