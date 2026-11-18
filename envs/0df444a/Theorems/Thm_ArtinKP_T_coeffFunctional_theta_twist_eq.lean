-- Prove2me | Theorems.Thm_ArtinKP_T_coeffFunctional_theta_twist_eq
-- name    : ArtinKP.T.coeffFunctional_theta_twist_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:45:33.866786+00:00
-- url     : https://prove2.me/theorems/751a8d0f-3af8-496a-818b-112abd6c9104
-- title:
--   ArtinKP.T.coeffFunctional_theta_twist_eq: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.T`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem coeffFunctional_theta_twist_eq (hν : ν ≠ 0) {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ (ν : F) M)
--       (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (hΓ : Inv Γ (Φ.twist hG hz6))
--       {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
--       (hfund : ∀ x : InfinitePlace F → ℂ,
--         ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
--       {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
--       (hper : ∀ β : 𝓞 F, β ∈ lamN Γ → chiInf (ν : F) (emb (β : F)) = 1)
--       {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
--       X.coeffFunctional Γ n (stripFn D (freq (ν : F)) φ) (measurable_stripFn hD _ hφ) 1
--           (norm_stripFn_le D _ hφ1) (C5.theta Γ (Φ.twist hG hz6))
--         = kap 𝔪 M * tau hG hz6 Φ ν * Wc D n φ (ν : F) (4 / 3)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B1.emb`, `ArtinKP.S.GSection` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.B.ValidDepth`, `ArtinKP.B.chiInf`, `ArtinKP.C5.Inv`, `ArtinKP.C5.theta`, `ArtinKP.N.lamN`, `ArtinKP.RF.measurable_stripFn`, `ArtinKP.RF.norm_stripFn_le`, `ArtinKP.RF.stripFn`, `ArtinKP.T.Wc`, `ArtinKP.T.freq`, `ArtinKP.T.kap`, `ArtinKP.T.tau`, `ArtinKP.X.GammaN`, `ArtinKP.X.GammaN.shift` and `ArtinKP.X.X.coeffFunctional` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero`, `ArtinKP.G2a.integral_strip_term`, `ArtinKP.G2a.thetaS_smul_gammaN`, `ArtinKP.G2a.thetaT_translate` and `ArtinKP.GK.hne` of this split import it.
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
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {ν}

theorem coeffFunctional_theta_twist_eq (hν : ν ≠ 0) {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ (ν : F) M)
    (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (hΓ : Inv Γ (Φ.twist hG hz6))
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ,
      ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    (hper : ∀ β : 𝓞 F, β ∈ lamN Γ → chiInf (ν : F) (emb (β : F)) = 1)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    X.coeffFunctional Γ n (stripFn D (freq (ν : F)) φ) (measurable_stripFn hD _ hφ) 1
        (norm_stripFn_le D _ hφ1) (C5.theta Γ (Φ.twist hG hz6))
      = kap 𝔪 M * tau hG hz6 Φ ν * Wc D n φ (ν : F) (4 / 3) := by
  sorry

end

end ArtinKP.T
end
