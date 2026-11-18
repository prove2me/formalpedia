-- Prove2me | Theorems.Thm_ArtinKP_T_integral_theta_of_hasCoef
-- name    : ArtinKP.T.integral_theta_of_hasCoef
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:46:07.593236+00:00
-- url     : https://prove2.me/theorems/b93f1e0e-4fa3-4e35-b680-3f7a24fcbc4c
-- title:
--   ArtinKP.T.integral_theta_of_hasCoef: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.T`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem integral_theta_of_hasCoef (hν : ν ≠ 0) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
--       (hΓ : Inv Γ (Φ.twist hG hz6)) {D : Set (InfinitePlace F → ℂ)} {κ : ℂ} {n : ℕ}
--       {φ : (InfinitePlace F → ℝ) → ℂ} (hc : HasCoef hG hz6 Φ ν D κ) (hDm : MeasurableSet D)
--       (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
--       ∫ Q in X.box n, conj (stripFn D (freq (ν : F)) φ Q)
--           * X.lift Γ (C5.theta Γ (Φ.twist hG hz6)) Q ∂X.vol F
--         = κ * tau hG hz6 Φ ν * Wc D n φ (ν : F) (4 / 3)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.X.box` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.lift` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.C5.Inv`, `ArtinKP.C5.theta`, `ArtinKP.RF.stripFn`, `ArtinKP.T.HasCoef`, `ArtinKP.T.Wc`, `ArtinKP.T.freq` and `ArtinKP.T.tau` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.GK.tau_eq_zero_of_theta`, `ArtinKP.GK.theta_per_gen_of_isExterior` and `ArtinKP.T.coeffFunctional_theta_twist_eq` of this split import it.
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

theorem integral_theta_of_hasCoef (hν : ν ≠ 0) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) {D : Set (InfinitePlace F → ℂ)} {κ : ℂ} {n : ℕ}
    {φ : (InfinitePlace F → ℝ) → ℂ} (hc : HasCoef hG hz6 Φ ν D κ) (hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    ∫ Q in X.box n, conj (stripFn D (freq (ν : F)) φ Q)
        * X.lift Γ (C5.theta Γ (Φ.twist hG hz6)) Q ∂X.vol F
      = κ * tau hG hz6 Φ ν * Wc D n φ (ν : F) (4 / 3) := by
  sorry

end

end ArtinKP.T
end
