-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_corollary_3
-- name    : EndToEndRisk.SquaredLoss.corollary_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:10.752541+00:00
-- url     : https://prove2.me/theorems/d0de6f7c-d2ec-4ee1-bec5-39fd2c351770
-- title:
--   Corollary 3, p. 22 — (R(g,ℙ) − R(ℙ))² ≤ B_X² (R_LS(g,ℙ) − R_LS(ℙ)): squared-loss excess risk bounds the optimality-gap excess risk
-- statement:
--   Let $X \subset \mathbb R^m$ be convex, compact and non-empty, let $f$ be convex and continuous on $X$, and let $x^*$ be a measurable selection of $\arg\min_{x \in X}\{f(x) + d^\top x\}$. Let $C \subset \mathbb R^m$ be bounded (Assumption 2). Let $(w,c)$ have joint law $\mathbb P$ on $W \times \mathbb R^m$ such that, for every $w$, the conditional law $\mathbb P[\cdot \mid w]$ is concentrated on $C$, is square integrable, and has mean $\mathbb E[c \mid w] \in \mathrm{Conv}(C)$, and such that $\mathbb E\|c\|_2^2 < \infty$. Write $R(g,\mathbb P)$ for the expected optimality gap $\mathbb E[L(g(w),c)]$ of a predictor $g$, $R_{\ell_{LS}}(g,\mathbb P) = \mathbb E\|g(w) - c\|_2^2$ for its squared-loss risk, and $R(\mathbb P)$, $R_{\ell_{LS}}(\mathbb P)$ for the infima over measurable predictors. Then for every measurable $g : W \to \mathbb R^m$,
--   $$\big(R(g,\mathbb P) - R(\mathbb P)\big)^2 \ \le\ B_X^2\,\big(R_{\ell_{LS}}(g,\mathbb P) - R_{\ell_{LS}}(\mathbb P)\big),$$
--   where $B_X$ is the Euclidean diameter of $X$. Equivalently, for $B_X > 0$, $\frac{1}{B_X^2}(R(g,\mathbb P) - R(\mathbb P))^2 \le R_{\ell_{LS}}(g,\mathbb P) - R_{\ell_{LS}}(\mathbb P)$.
--
--   A predictor trained only by least squares, without any knowledge of $f$ or $X$, therefore has excess optimality-gap risk at most $B_X$ times the square root of its excess squared-loss risk.
--
--   **Formalization Note** The factor $1/B_X^2$ is multiplied out: for $B_X > 0$ this is equivalent, and for a one-point $X$ (where the printed expression is undefined) both sides are trivially consistent since $L \equiv 0$. Risks are $[0,\infty]$-valued and excess risks are truncated differences; the hypothesis $\mathbb E\|c\|_2^2 < \infty$ is added because without it $R_{\ell_{LS}}(\mathbb P)$ may be infinite (conditional variances unbounded in $w$), where the paper's expression is $\infty - \infty$. Measurability of $x^*$ and $g$ is added (the paper works up to Lebesgue measurability). Assumption 2 is part of the section's standing hypotheses (it enters through Theorem 3).
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 22, Corollary 3 (proof p. ec10)

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Corollary 3, p. 22 (proof p. ec10): for the squared loss,
`(1/B_X²) (R(g, ℙ) − R(ℙ))² ≤ R_{ℓ_LS}(g, ℙ) − R_{ℓ_LS}(ℙ)`, stated multiplied out by `B_X²`. -/
theorem corollary_3 {m : ℕ} {W : Type*} [MeasurableSpace W]
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C)
    (μ : Measure W) [IsProbabilityMeasure μ]
    (κ : Kernel W (EuclideanSpace ℝ (Fin m))) [IsMarkovKernel κ]
    (hκ : ∀ w, κ w ∈ lsClass C)
    (hsq : ∫⁻ p, ‖p.2‖ₑ ^ 2 ∂(μ ⊗ₘ κ) < ⊤)
    (g : W → EuclideanSpace ℝ (Fin m)) (hg : Measurable g) :
    (risk (trueLoss X f xstar) (μ ⊗ₘ κ) g - bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ)) ^ 2 ≤
      ENNReal.ofReal (Metric.diam X ^ 2) *
        (risk lsLoss (μ ⊗ₘ κ) g - bayesRisk lsLoss (μ ⊗ₘ κ)) := by sorry

end EndToEndRisk.SquaredLoss
