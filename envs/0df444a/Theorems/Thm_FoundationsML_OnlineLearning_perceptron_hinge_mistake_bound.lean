-- Prove2me | Theorems.Thm_FoundationsML_OnlineLearning_perceptron_hinge_mistake_bound
-- name    : FoundationsML.OnlineLearning.perceptron_hinge_mistake_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:23:35.005513+00:00
-- url     : https://prove2.me/theorems/798f9105-c75a-4dc4-8412-c716a28fa7b4
-- title:
--   Theorem 8.11 — Perceptron hinge-loss mistake bound
-- statement:
--   **Statement (Theorem 8.11, p. 196, PDF p. 213).** Let $I$ be the set of indices at which
--   the Perceptron algorithm updates while processing $x_1,\dots,x_T$ with $\|x_t\|\le r$. Then
--   $M=|I|$ satisfies $M \le \inf_{\rho>0,\|v\|_2\le1}
--   [(r/\rho+\sqrt{r^2/\rho^2+4\|l_\rho\|_1})/2]^2$, where $l_\rho=(l_t)_{t\in I}$,
--   $l_t=\max\{0,1-y_t(v\cdot x_t)/\rho\}$. The non-separable generalization of Theorem 8.8's
--   separable-case margin mistake bound, in terms of an arbitrary comparator $v$'s hinge losses.
--
--   **Formalization Note.** The `inf` over `ρ>0, ‖v‖₂≤1` is kept in the statement (via nested
--   restricted `⨅`, `Set.Ioi 0` and `Metric.closedBall 0 1`), per `BRIEF.md`'s pitfall note
--   that fixing `ρ`, `v` in advance is a weaker, different claim. Only the theorem's first
--   (tighter, `L¹`-norm) displayed inequality is drafted; the second, looser chained
--   inequality is a further corollary the book states immediately after, not drafted
--   separately (disclosed in `description.md`).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 196, Theorem 8.11 (PDF p. 213)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronNumUpdates
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronUpdates

namespace FoundationsML.OnlineLearning

/-- Theorem 8.11 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 196, PDF p. 213). Let `I` be the set of update rounds of the Perceptron
algorithm processing `x_1,…,x_T` with `‖x_t‖ ≤ r`. Then `M = |I|` satisfies
`M ≤ inf_{ρ>0, ‖v‖₂≤1} [(r/ρ + sqrt(r²/ρ² + 4‖l_ρ‖₁))/2]²`, where
`l_ρ = (l_t)_{t∈I}` with `l_t = max{0, 1 − y_t(v·x_t)/ρ}`. -/
theorem perceptron_hinge_mistake_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (T : ℕ) (r : ℝ) (hr : 0 < r) (hxr : ∀ t < T, ‖x t‖ ≤ r) :
    (PerceptronNumUpdates x y T : ℝ) ≤
      ⨅ ρ ∈ Set.Ioi (0 : ℝ), ⨅ v ∈ Metric.closedBall (0 : V) 1,
        ((r / ρ + Real.sqrt (r ^ 2 / ρ ^ 2 +
            4 * ∑ t ∈ PerceptronUpdates x y T,
              max 0 (1 - y t * (inner (𝕜 := ℝ) v (x t) : ℝ) / ρ))) /
          2) ^ 2 := by sorry

end FoundationsML.OnlineLearning
