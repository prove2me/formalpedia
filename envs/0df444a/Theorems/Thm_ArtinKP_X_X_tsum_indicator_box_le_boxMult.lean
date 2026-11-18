-- Prove2me | Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult
-- name    : ArtinKP.X.X.tsum_indicator_box_le_boxMult
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:21:22.932947+00:00
-- url     : https://prove2.me/theorems/636442b9-719e-466d-ab47-b3e1107336c2
-- title:
--   ArtinKP.X.X.tsum_indicator_box_le_boxMult: a Γ-orbit meets the n-th box at most X.boxMult Γ n times
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **In words.** Let $F$ be a number field, $X$ (`ArtinKP.X.X` $F$) the product over the infinite places $w$ of $F$ (real and complex alike) of copies of hyperbolic 3-space $\mathbb H^3=\{(x,v): x\in\mathbb C,\ v>0\}$, with $\mathrm{SL}_2(\mathcal O_F)$ acting factorwise by Möbius transformations through the complex embeddings, and $\Gamma$ any subgroup of $\mathrm{SL}_2(\mathcal O_F)$. For $n\in\mathbb N$ the box `ArtinKP.X.X.box` $n$ is the set of points all of whose coordinates $(x_w,v_w)$ satisfy $|x_w|\le n$ and $1/(n+1)\le v_w\le n+1$ (built from `ArtinKP.X.H3.box`). The number `ArtinKP.X.X.boxMult` $\Gamma\,n$ is the number of elements $\gamma\in\Gamma$ that map some point of the $n$-th box into the $n$-th box (a finite set, by `ArtinKP.X.finite_return_box`). The statement: for every $n$ and every point $P\in X$,
--   $$\sum_{\gamma\in\Gamma}\mathbf 1_{\mathrm{box}(n)}(\gamma\cdot P)\ \le\ \mathrm{boxMult}(\Gamma,n),$$
--   the sum taken in $[0,\infty]$; that is, at most $\mathrm{boxMult}(\Gamma,n)$ elements of $\Gamma$ move $P$ into the $n$-th box. The point $P$ need not lie in the box.
--
--   **Role in the argument.** With this multiplicity bound, restriction of a $\Gamma$-invariant function to a box is a bounded operator from $L^2(\Gamma\backslash X)$ to $L^2$ of the box; the Fourier-coefficient and constant-term arguments integrate theta and Eisenstein series over boxes through it.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal`, `open MeasureTheory Set NumberField`):
--
--   ```lean
--   lemma X.tsum_indicator_box_le_boxMult (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (P : X F) :
--       ∑' γ : Γ, (X.box n : Set (X F)).indicator (fun _ => (1 : ℝ≥0∞)) (γ • P) ≤ (X.boxMult Γ n : ℝ≥0∞)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.X.box` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.X.boxMult` (definitions bundle `ArtinKPB007` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero`, `ArtinKP.C9.theta_psiSum_ne_zero`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.G2a.integral_strip_term`, `ArtinKP.G2a.thetaS_smul_gammaN`, `ArtinKP.G2a.thetaT_translate`, `ArtinKP.GK.hne`, `ArtinKP.GK.kw_theta_of_diffInS`, `ArtinKP.GK.tau_eq_zero_of_theta`, `ArtinKP.GK.theta_per_gen_of_isExterior`, `ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N.Acoef_eq`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.coeff_resPart_add_hInt`, `ArtinKP.N.differentiableOn_Acoef`, `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray`, `ArtinKP.N.lift_theta_translate`, `ArtinKP.N.tendsto_ray_Acoef`, `ArtinKP.T.coeffFunctional_theta_twist_eq`, `ArtinKP.T.differentiableOn_Afun`, `ArtinKP.T.hasResOn_kubota_aSer`, `ArtinKP.T.integral_theta_of_hasCoefT`, `ArtinKP.T.resSlit_add_of_seed`, `ArtinKP.T.resSlit_mul_of_seed`, `ArtinKP.T.tendsto_ray_Afun` and `ArtinKP.X.X.dense_range_coreL2` and the definitions bundle `ArtinKPB015` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB007

section

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.tsum_indicator_box_le_boxMult (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (P : X F) :
    ∑' γ : Γ, (X.box n : Set (X F)).indicator (fun _ => (1 : ℝ≥0∞)) (γ • P) ≤ (X.boxMult Γ n : ℝ≥0∞) := by
  sorry

end

end ArtinKP.X
end
