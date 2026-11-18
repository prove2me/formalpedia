-- Prove2me | Theorems.Thm_ArtinKP_N_integral_box_theta_eq_of_tendsto_ray
-- name    : ArtinKP.N.integral_box_theta_eq_of_tendsto_ray
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:45:42.640005+00:00
-- url     : https://prove2.me/theorems/55601c8d-2509-4c67-b66f-fb04df6f5a86
-- title:
--   ArtinKP.N.integral_box_theta_eq_of_tendsto_ray: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.N`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF`):
--
--   ```lean
--   theorem integral_box_theta_eq_of_tendsto_ray (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
--       {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) (n : ℕ)
--       (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) {a : ℂ → ℂ}
--       (ha : DifferentiableOn ℂ a E.slit)
--       (heq : ∀ s : ℂ, 2 < s.re → a s = ∫ P in X.box n, conj (ψ P) * eis Ψ s P ∂X.vol F) {r : ℂ}
--       (hr : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * a (ray t)) (𝓝[>] 0) (𝓝 r)) :
--       ∫ P in X.box n, conj (ψ P) * X.lift Γ (theta Γ Ψ) P ∂X.vol F = r
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.X.box` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.lift` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.B.eis`, `ArtinKP.C5.EisEigen`, `ArtinKP.C5.Inv`, `ArtinKP.C5.theta`, `ArtinKP.E.slit` and `ArtinKP.N.ray` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.C9.theta_psiSum_ne_zero`, `ArtinKP.F.zPsi_add`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.F.zPsi_smul`, `ArtinKP.G2a.thetaT_translate`, `ArtinKP.GK.kw_theta_of_diffInS`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.lift_theta_translate` and `ArtinKP.N.zRes_eq_of_continuation` of this split import it.
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
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

theorem integral_box_theta_eq_of_tendsto_ray (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) (n : ℕ)
    (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) {a : ℂ → ℂ}
    (ha : DifferentiableOn ℂ a E.slit)
    (heq : ∀ s : ℂ, 2 < s.re → a s = ∫ P in X.box n, conj (ψ P) * eis Ψ s P ∂X.vol F) {r : ℂ}
    (hr : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * a (ray t)) (𝓝[>] 0) (𝓝 r)) :
    ∫ P in X.box n, conj (ψ P) * X.lift Γ (theta Γ Ψ) P ∂X.vol F = r := by
  sorry

end

end ArtinKP.N
end
