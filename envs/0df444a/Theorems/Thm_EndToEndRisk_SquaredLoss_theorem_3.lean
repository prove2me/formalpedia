-- Prove2me | Theorems.Thm_EndToEndRisk_SquaredLoss_theorem_3
-- name    : EndToEndRisk.SquaredLoss.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:20.16441+00:00
-- url     : https://prove2.me/theorems/e739f1e1-8d4a-47b2-8a3a-dfd309ea1e45
-- title:
--   Theorem 3, p. 20 — uniform calibration gives δ∗∗_ℓ(R(g,ℙ) − R(ℙ);𝒫) ≤ R_ℓ(g,ℙ) − R_ℓ(ℙ), with δ∗∗ > 0 on (0, B_f + B_C B_X]
-- statement:
--   Let $X$, $f$ and a measurable argmin selection $x^*$ be as in the standing setting, and let $C$ be bounded (Assumption 2). Let $\ell \ge 0$ be a measurable surrogate loss and $Q$ a class of integrable probability laws of $c$ concentrated on $C$ with means in $\mathrm{Conv}(C)$, and suppose $\ell$ is $Q$-uniformly calibrated. Put $B = B_f + B_C B_X$ and let $\delta^{**}_\ell(\cdot; Q)$ be the largest convex minorant of $\delta_\ell(\cdot; Q)$ on $(0, B]$ that is non-positive at $0$. Then:
--
--   1. $\delta^{**}_\ell(\epsilon; Q) > 0$ for every $\epsilon \in (0, B]$;
--   2. for every joint law $\mathbb P$ of $(w,c)$ whose conditional laws $\mathbb P[\cdot \mid w]$ all lie in $Q$, whose surrogate Bayes risk is finite and equals $\mathbb E[\inf_{d'}\mathbb E[\ell(d',c) \mid w]]$, and for every measurable predictor $g : W \to \mathbb R^m$,
--   $$\delta^{**}_\ell\big(R(g,\mathbb P) - R(\mathbb P); Q\big) \ \le\ R_\ell(g,\mathbb P) - R_\ell(\mathbb P).$$
--
--   Any uniformly calibrated surrogate therefore controls the excess optimality-gap risk through its own excess risk, by a function that does not depend on $\mathbb P$.
--
--   **Formalization Note** Several hypotheses are added and disclosed. $\ell \ge 0$ and measurability of $\ell$ (the paper asks for both, pp. 10 and 19). $R_\ell(\mathbb P) < \infty$, because excess risks are truncated differences in $[0,\infty]$. The identity $R_\ell(\mathbb P) = \mathbb E[\inf_{d'}\mathbb E[\ell(d',c) \mid w]]$, which Steinwart's Theorem 2.13 (used in the proof) obtains from a measurable selection on a complete measurable space. Measurability of $x^*$ and of $g$. The function $\delta^{**}$ includes the constraint $h'(0) \le 0$, the convention $\delta_\ell(0) = 0$ of p. 19; the printed definition constrains $h'$ only on $(0, B]$, which admits positive constants and makes the inequality false at $g = g^*$. The excess true risk is finite under these hypotheses and is passed to $\delta^{**}$ as a real number.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, p. 20, Theorem 3 (proof p. ec9); δ(0) = 0 convention p. 19

import Mathlib
import Definitions.Def_EndToEndRisk_SquaredLoss_Setting

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Theorem 3, p. 20 (proof p. ec9): if `ℓ` is `Q`-uniformly calibrated and Assumption 2 holds,
then `δ∗∗_ℓ(ε; Q)` (with `δ_ℓ(0) = 0`, p. 19) is positive on `(0, B_f + B_C B_X]`, and for every
joint law `ℙ = μ ⊗ κ` with conditional laws in `Q` and every measurable predictor `g`,
`δ∗∗_ℓ(R(g, ℙ) − R(ℙ); Q) ≤ R_ℓ(g, ℙ) − R_ℓ(ℙ)`. -/
theorem theorem_3 {m : ℕ} {W : Type*} [MeasurableSpace W]
    (X : Set (EuclideanSpace ℝ (Fin m))) (f : EuclideanSpace ℝ (Fin m) → ℝ) (hS : Standing X f)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hx : IsArgminSelection X f xstar) (hxm : Measurable xstar)
    (C : Set (EuclideanSpace ℝ (Fin m))) (hA2 : Bornology.IsBounded C)
    (ℓ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hℓm : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ d c, 0 ≤ ℓ d c)
    (Q : Set (Measure (EuclideanSpace ℝ (Fin m))))
    (hQ : ∀ ν ∈ Q, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
      Integrable (fun c => c) ν ∧
      (∫ c, c ∂ν) ∈ convexHull ℝ C)
    (hUC : UniformlyCalibrated ℓ (trueLoss X f xstar) Q) :
    (∀ ε ∈ Set.Ioc 0 (Bf X f + Bc C * Metric.diam X),
        0 < deltaBiconj (deltaL ℓ (trueLoss X f xstar) Q) (Bf X f + Bc C * Metric.diam X) ε) ∧
      ∀ (μ : Measure W) [IsProbabilityMeasure μ]
        (κ : Kernel W (EuclideanSpace ℝ (Fin m))) [IsMarkovKernel κ],
        (∀ w, κ w ∈ Q) →
        bayesRisk ℓ (μ ⊗ₘ κ) = ∫⁻ w, ⨅ d', condRisk ℓ (κ w) d' ∂μ →
        bayesRisk ℓ (μ ⊗ₘ κ) < ⊤ →
        ∀ g : W → EuclideanSpace ℝ (Fin m), Measurable g →
          deltaBiconj (deltaL ℓ (trueLoss X f xstar) Q) (Bf X f + Bc C * Metric.diam X)
              (risk (trueLoss X f xstar) (μ ⊗ₘ κ) g -
                bayesRisk (trueLoss X f xstar) (μ ⊗ₘ κ)).toReal ≤
            risk ℓ (μ ⊗ₘ κ) g - bayesRisk ℓ (μ ⊗ₘ κ) := by sorry

end EndToEndRisk.SquaredLoss
