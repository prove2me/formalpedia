-- Prove2me | Theorems.Thm_ConicBlackwell_display_11
-- name    : ConicBlackwell.display_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:16.995611+00:00
-- url     : https://prove2.me/theorems/a072ed7d-ed59-4573-a6bd-22433e7dfe94
-- title:
--   Display (11) — weighted regret $\le\sqrt2\,\kappa\, d\big(\sum_t\theta_tv_t,\mathcal C^\circ\big)$
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $\kappa=\max_{x\in\mathcal X}\|x\|_2$, $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)$ and $\mathcal C^\circ$ its polar. For every horizon $T$, all real weights $\theta_1,\dots,\theta_T$, losses $f_1,\dots,f_T\in\mathbb R^n$ and decisions $x_1,\dots,x_T\in\mathcal X$, with payoffs $v_t=(\langle f_t,x_t\rangle/\kappa,\,-f_t)$,
--
--   $$
--   \sum_{t=1}^T\theta_t\langle f_t,x_t\rangle-\min_{x\in\mathcal X}\sum_{t=1}^T\theta_t\langle f_t,x\rangle\ \le\ \sqrt2\,\kappa\cdot d\Big(\sum_{t=1}^T\theta_tv_t,\ \mathcal C^\circ\Big).
--   $$
--
--   This reduces the regret of any decision sequence to the distance of its weighted payoff vector from the target cone $\mathcal C^\circ$, the quantity Blackwell approachability controls.
--
--   Differences from the source:
--   - generalization: the decisions x_t of a CBA+ run with weights θ_t > 0 and T ≥ 1 → any decisions x_t ∈ X (1 ≤ t ≤ T), any real θ_t, any T ∈ ℕ; reason: the inequality uses only x_t ∈ X and is linear in θ; the CBA+ run has x_t ∈ X (u_t ∈ C), and T = 0 gives 0 ≤ 0
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: κ = max_{x∈X} ‖x‖₂ and v_t = (⟨f_t, x_t⟩/κ, −f_t) → kappa X = sSup of ‖x‖ over X, and payoff X x f = lift (⟪f, x⟫ / kappa X) (−f) with Lean's x/0 = 0; reason: sSup is the max on a nonempty compact X; κ = 0 only when X = {0}, where the page's ⟨f,x⟩/κ is undefined and both coordinates conventions give the same statement
--   - encoding: min_{x∈X} Σ_{t=1}^T θ_t⟨f_t, x⟩ → sInf of the image of X (weightedRegret); reason: a continuous function on a nonempty compact X attains its infimum
--   - encoding: d(u, S) → Metric.infDist u S; reason: the Euclidean distance to a set
--   - encoding: rounds t ≥ 1 of Algorithm 1 → sequences ℕ → ·, with rounds t ∈ Finset.Icc 1 T; values at index 0 unused (u 0 = 0 is the start of the run); reason: Lean convention; same instances
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), proof of Theorem 3.3, display (11), p.9

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_weightedRegret
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **Display (11)** (proof of Theorem 3.3), Grand-Clément & Kroer, arXiv:2202.12277v1, p.9:
`Σ_{t=1}^T θ_t⟨f_t, x_t⟩ − min_{x∈X} Σ_{t=1}^T θ_t⟨f_t, x⟩ ≤ √2 κ · d(Σ_{t=1}^T θ_t v_t, C°)`,
with `v_t = (⟨f_t, x_t⟩/κ, −f_t)`.

Formalization Note: stated for every sequence of decisions `x_t ∈ X` (`1 ≤ t ≤ T`), every real
weights `θ` and every loss sequence, not only for the CBA+ run (the run is a special case);
`v_t = payoff X (x t) (f t)`, `C° = target X`, `κ = kappa X`, the min is `sInf`
(`weightedRegret`). -/
theorem display_11 {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (θ : ℕ → ℝ) (f x : ℕ → E n) (T : ℕ) (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ X) :
    weightedRegret X θ f x T ≤
      Real.sqrt 2 * kappa X *
        Metric.infDist (∑ t ∈ Finset.Icc 1 T, θ t • payoff X (x t) (f t)) (target X) := by sorry

end ConicBlackwell
