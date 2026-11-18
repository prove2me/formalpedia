-- Prove2me | Theorems.Thm_ArtinKP_C5_tendsto_ray_functional_resPart_theta
-- name    : ArtinKP.C5.tendsto_ray_functional_resPart_theta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:43:50.451988+00:00
-- url     : https://prove2.me/theorems/1eeb5c87-c5fc-4675-8d66-3383cd931f48
-- title:
--   ArtinKP.C5.tendsto_ray_functional_resPart_theta: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.C5`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs`):
--
--   ```lean
--   theorem tendsto_ray_functional_resPart_theta (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
--       {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (ℓ : X.L2 Γ →L[ℂ] ℂ) :
--       Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) *
--         ℓ (resPart Γ Ψ ((4 / 3 : ℂ) + t * (1 + Complex.I)))) (𝓝[>] 0) (𝓝 (ℓ (theta Γ Ψ)))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.C5.Inv`, `ArtinKP.C5.resPart` and `ArtinKP.C5.theta` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.G2a.thetaT_translate`, `ArtinKP.GK.kw_theta_of_diffInS`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray`, `ArtinKP.N.lift_theta_translate`, `ArtinKP.N.tendsto_ray_Acoef` and `ArtinKP.T.tendsto_ray_Afun` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
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

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

variable [IsTotallyComplex F]

theorem tendsto_ray_functional_resPart_theta (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (ℓ : X.L2 Γ →L[ℂ] ℂ) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) *
      ℓ (resPart Γ Ψ ((4 / 3 : ℂ) + t * (1 + Complex.I)))) (𝓝[>] 0) (𝓝 (ℓ (theta Γ Ψ))) := by
  sorry

end

end ArtinKP.C5
end
