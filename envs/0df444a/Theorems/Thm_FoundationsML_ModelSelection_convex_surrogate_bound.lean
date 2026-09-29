-- Prove2me | Theorems.Thm_FoundationsML_ModelSelection_convex_surrogate_bound
-- name    : FoundationsML.ModelSelection.convex_surrogate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:24:56.423991+00:00
-- url     : https://prove2.me/theorems/40f4a36e-6332-4973-88e4-252d8c9b4832
-- title:
--   Theorem 4.7 — Excess-error bound via a convex surrogate loss
-- statement:
--   **Statement (Theorem 4.7, p. 76, PDF p. 93).** Let $\Phi$ be convex and non-decreasing.
--   Assume there exist $s\ge1$, $c>0$ with $|h^*(x)|^s \le c^s(L_\Phi(x,0)-L_\Phi(x,h^*_\Phi(x)))$
--   for all $x\in X$, where $h^*_\Phi$ is the (pointwise) minimizer of $u\mapsto L_\Phi(x,u)$.
--   Then, for any hypothesis $h:X\to\mathbb R$:
--   $$R(h) - R^* \le 2c\big(L_\Phi(h)-L^*_\Phi\big)^{1/s}.$$
--   This is what makes convex-surrogate-based algorithms (hinge loss, exponential loss, logistic
--   loss) theoretically justified: minimizing the convex surrogate's excess loss controls the
--   true (non-convex) excess classification error.
--
--   **Formalization Note.** `hΦstar : X → ℝ` is taken as a real-valued pointwise minimizer of
--   `PhiLossPointwise η Φ x ·` (hypothesis `hΦstar_min`); the book's own degenerate case
--   `h*_Φ(x) = ±∞` at $\eta(x)\in\{0,1\}$ is outside a real-valued formalization and is not
--   covered (disclosed in `description.md`/`MODERATION_NOTES.md` — the minimizing hypothesis is
--   simply unsatisfiable by a real-valued function exactly at those points, so the theorem
--   applies whenever such a real-valued `hΦstar` is supplied). `ConvexOn ℝ Set.univ Φ` and
--   `Monotone Φ` match "convex and non-decreasing" exactly; `R(h)` and `R*=R(h^*)` are both
--   instances of `ScoringRisk`, with `BayesScore η` standing for `h^*`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 76, Theorem 4.7 (PDF p. 93)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_BayesScore
import Definitions.Def_FoundationsML_ModelSelection_PhiLossPointwise
import Definitions.Def_FoundationsML_ModelSelection_ExpectedPhiLoss
import Definitions.Def_FoundationsML_ModelSelection_ScoringRisk

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Theorem 4.7 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 76, PDF p. 93). Let `Φ : ℝ → ℝ` be convex and non-decreasing, and let
`hΦstar` be a pointwise minimizer of the Φ-loss `u ↦ L_Φ(x, u)` at every `x` (the book's
`h*_Φ`, taken here as a real-valued function; the book's own use of `h*_Φ(x) = ±∞` at the
degenerate points `η(x) ∈ {0, 1}` is outside this real-valued formalization). Assume there
exist `s ≥ 1` and `c > 0` with `|h*(x)|^s ≤ c^s (L_Φ(x,0) − L_Φ(x,h*_Φ(x)))` for all `x`, where
`h*(x) = η(x) − 1/2` is the Bayes scoring function. Then, for any hypothesis `h : X → ℝ`,
`R(h) − R* ≤ 2c (L_Φ(h) − L*_Φ)^{1/s}`. -/
theorem convex_surrogate_bound {X : Type*} [MeasurableSpace X] (DX : Measure X)
    [IsProbabilityMeasure DX] (η : X → ℝ) (Φ : ℝ → ℝ)
    (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hΦstar : X → ℝ)
    (hΦstar_min : ∀ x u, PhiLossPointwise η Φ x (hΦstar x) ≤ PhiLossPointwise η Φ x u)
    (s c : ℝ) (hs : 1 ≤ s) (hc : 0 < c)
    (hbound : ∀ x, |BayesScore η x| ^ s ≤
      c ^ s * (PhiLossPointwise η Φ x 0 - PhiLossPointwise η Φ x (hΦstar x)))
    (h : X → ℝ) :
    ScoringRisk DX η h - ScoringRisk DX η (BayesScore η) ≤
      2 * c * (ExpectedPhiLoss DX η Φ h - ExpectedPhiLoss DX η Φ hΦstar) ^ (1 / s) := by sorry

end FoundationsML.ModelSelection
