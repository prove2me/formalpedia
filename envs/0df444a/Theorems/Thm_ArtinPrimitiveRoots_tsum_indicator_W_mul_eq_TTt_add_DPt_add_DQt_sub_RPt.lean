-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt
-- name    : ArtinPrimitiveRoots.tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T10:53:02.086165+00:00
-- url     : https://prove2.me/theorems/c3e4f66f-48cf-4f32-b10b-ecba4b7c70fb
-- title:
--   The explicit formula for one pair in Goldmakher–Louvel's Σ₃ — the smoothed sum of ψ over s(𝔞) > L is T − T′ + DP + DQ − RP
-- statement:
--   Let $F$ be a number field, let $\mathfrak m, \mathfrak g, \mathfrak c$ be nonzero ideals of $\mathcal O_F$ with $\mathfrak m \ne \mathcal O_F$, $\mathfrak g + \mathfrak m = \mathcal O_F$ and $\mathfrak g + \mathfrak c = \mathcal O_F$, let $\psi$ satisfy `GLW.PsiHyp 𝔪 c ψ`, and let $\Lambda$ satisfy `GLW.LamHyp 𝔪 c ψ Λ` (bundle `Def_ArtinGLWeight`). Let $M > 0$, let $L, L'$ be real, and let $0 < \varepsilon, \varepsilon' < 1/2$ and $\sigma_1 > 0$ with $\sigma_1$ not an integer. Then
--   $$\sum_{\substack{\mathfrak a + \mathfrak g = \mathcal O_F\\ \texttt{sgt}\ L\ \mathfrak a}} W\Big(\frac{q_{\mathfrak a}}{M}\Big)\psi(\mathfrak a) = \texttt{TTt} + \texttt{DPt} + \texttt{DQt} - \texttt{RPt},$$
--   the sum over all ideals $\mathfrak a$ (a `tsum`), where $W$ is `GLW.W`, $q_{\mathfrak a}$ is the absolute norm, and the four terms are `GLW.TTt 𝔪 𝔤 c ψ M L L'`, `GLW.DPt 𝔪 𝔤 c ψ M L' ε'`, `GLW.DQt 𝔪 𝔤 c ψ M L' σ₁` and `GLW.RPt 𝔪 𝔤 c ψ M L ε`.
--
--   This is the explicit formula for the row sum of one pair of columns in the proof of Proposition 5.2 of L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370 (their §6.2–6.3, for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38). With $\psi = \chi_{\mathfrak c_1}\chi_{\mathfrak c_2}$ and $\mathfrak c = \mathfrak c_1\mathfrak c_2$, the left side is the row sum of their $\Sigma_3$ for the pair $(\mathfrak g\mathfrak c_1, \mathfrak g\mathfrak c_2)$. The four terms are in the bundle's prose: `TTt` is the difference of the two main terms, `DPt` and `DQt` are the two parts of the dual sum, and `RPt` is the remainder of the part with $s(\mathfrak a) \le L$. The terms differ from their (6.3), as the bundle's formalization note says.
--
--   It is a cut for `exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le` (their Proposition 5.2), together with `norm_PSnp_RPt_le_and_norm_PSnp_DPt_le_and_norm_PSnp_DQt_le_and_norm_PSnp_TTt_le` and `exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation`.
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, §6.2–6.3, the explicit formula for one pair of columns (the smoothed row sum over s(𝔞) > L as T − T′ + DP + DQ − RP; a cut for Proposition 5.2)

import Mathlib
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinGLWeight

namespace ArtinPrimitiveRoots

open NumberField

theorem tsum_indicator_W_mul_eq_TTt_add_DPt_add_DQt_sub_RPt (F : Type*) [Field F] [NumberField F]
    (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (Λ : ℂ → ℂ) (hψ : GLW.PsiHyp 𝔪 c ψ)
    (hΛ : GLW.LamHyp 𝔪 c ψ Λ) (h𝔤 : 𝔤 ≠ ⊥) (h𝔪0 : 𝔪 ≠ ⊥) (h𝔪t : 𝔪 ≠ ⊤) (hc : c ≠ ⊥)
    (h𝔤m : 𝔤 ⊔ 𝔪 = ⊤) (h𝔤c : 𝔤 ⊔ c = ⊤) (M : ℝ) (hM : 0 < M) (L L' ε ε' σ₁ : ℝ)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hε' : 0 < ε') (hε'2 : ε' < 1 / 2) (hσ₁ : 0 < σ₁)
    (hσint : ∀ m : ℕ, σ₁ ≠ m) :
    ∑' a : Ideal (𝓞 F), ({a | a ⊔ 𝔤 = ⊤ ∧ GLW.sgt L a} : Set (Ideal (𝓞 F))).indicator
        (fun a => (GLW.W ((Ideal.absNorm a : ℝ) / M) : ℂ) * ψ a) a =
      GLW.TTt 𝔪 𝔤 c ψ M L L' + GLW.DPt 𝔪 𝔤 c ψ M L' ε' + GLW.DQt 𝔪 𝔤 c ψ M L' σ₁ -
        GLW.RPt 𝔪 𝔤 c ψ M L ε := by
  sorry

end ArtinPrimitiveRoots
