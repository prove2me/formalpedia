-- Prove2me | Theorems.Thm_ArtinKP_X_X_isPOU_pou
-- name    : ArtinKP.X.X.isPOU_pou
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:24:41.193416+00:00
-- url     : https://prove2.me/theorems/adf9ec74-b335-40c4-8a7f-f58b616c8e26
-- title:
--   ArtinKP.X.X.isPOU_pou: the chosen function X.pou Γ is a partition of unity for Γ on X
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **In words.** Let $F$ be a number field, $X$ (`ArtinKP.X.X` $F$) the product over the infinite places of $F$ (real and complex alike) of copies of hyperbolic 3-space $\mathbb H^3=\{(x,v): x\in\mathbb C,\ v>0\}$, with $\mathrm{SL}_2(\mathcal O_F)$ acting factorwise by Möbius transformations through the complex embeddings, and $\Gamma$ any subgroup of $\mathrm{SL}_2(\mathcal O_F)$. The function `ArtinKP.X.X.pou` $\Gamma : X\to[0,\infty]$ is defined as a choice of an everywhere positive partition of unity, whose existence is `ArtinKP.X.exists_isPOU_forall_pos`. The statement says that this chosen function satisfies `ArtinKP.X.IsPOU` for $\Gamma$: writing $\eta$ for it, $\eta$ is measurable and $\sum_{\gamma\in\Gamma}\eta(\gamma\cdot P)=1$ for every $P\in X$ (sum in $[0,\infty]$); the sum runs over the elements of $\Gamma$, so when $-1\in\Gamma$, which acts trivially on $X$, every orbit point is counted at least twice.
--
--   **Role in the argument.** The quotient measure `ArtinKP.X.X.quotVol` $\Gamma$ on $\Gamma\backslash X$, and with it the Hilbert space `ArtinKP.X.X.L2` $\Gamma=L^2(\Gamma\backslash X)$ on which the self-adjoint Laplacian acts and in which the theta function is constructed, is defined from `ArtinKP.X.X.pou` $\Gamma$; this is the property every unfolding computation uses.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal`, `open MeasureTheory Set NumberField`):
--
--   ```lean
--   lemma X.isPOU_pou (Γ : Subgroup (SL(2, 𝓞 F))) : IsPOU Γ (X.pou Γ)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.IsPOU` (definitions bundle `ArtinKPB008` of this split); `ArtinKP.X.X.pou` (definitions bundle `ArtinKPB009` of this split).
--
--   **Used by.** The proofs of `ArtinKP.B1.lintegral_G_pow_lt_top`, `ArtinKP.C5.differentiableOn_functional_resPart`, `ArtinKP.C5.quotVol_lt_top`, `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero`, `ArtinKP.C9.theta_psiSum_ne_zero`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.G2a.integral_strip_term`, `ArtinKP.G2a.thetaS_smul_gammaN`, `ArtinKP.G2a.thetaT_translate`, `ArtinKP.GK.hne`, `ArtinKP.GK.kw_theta_of_diffInS`, `ArtinKP.GK.tau_eq_zero_of_theta`, `ArtinKP.GK.theta_per_gen_of_isExterior`, `ArtinKP.N2.integrable_lift_pou`, `ArtinKP.N2.lintegral_lift_pou_ne_top`, `ArtinKP.N2.orbit_integral_eq_zero`, `ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N.Acoef_eq`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.coeff_resPart_add_hInt`, `ArtinKP.N.differentiableOn_Acoef`, `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray`, `ArtinKP.N.lift_theta_translate`, `ArtinKP.N.tendsto_ray_Acoef`, `ArtinKP.RC.lintegral_G_pow_lt_top`, `ArtinKP.T.coeffFunctional_theta_twist_eq`, `ArtinKP.T.differentiableOn_Afun`, `ArtinKP.T.hasResOn_kubota_aSer`, `ArtinKP.T.integral_theta_of_hasCoefT`, `ArtinKP.T.resSlit_add_of_seed`, `ArtinKP.T.resSlit_mul_of_seed`, `ArtinKP.T.tendsto_ray_Afun`, `ArtinKP.X.X.coreL2_injective`, `ArtinKP.X.X.dense_range_coreL2`, `ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff`, `ArtinKP.X.X.ims`, `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreLap_coreL2`, `ArtinKP.X.X.inner_coreLap_eq`, `ArtinKP.X.X.integrable_pou_mul` and `ArtinKP.X.X.l2Rep_of_mem_core` and the definitions bundles `ArtinKPB010` and `ArtinKPB015` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB009

section

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.isPOU_pou (Γ : Subgroup (SL(2, 𝓞 F))) : IsPOU Γ (X.pou Γ) := by
  sorry

end

end ArtinKP.X
end
