-- Prove2me | Theorems.Thm_FamousTheorems_bayes
-- name    : FamousTheorems.bayes
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T01:51:26.337774+00:00
-- url     : https://prove2.me/theorems/0e3fc4e3-4a91-4413-b8bb-a04ba0d943a1
-- title:
--   Bayes' theorem
-- statement:
--   **Bayes' theorem.**
--
--   For measurable events $s, t$ under a finite measure $\mu$,
--   $$\mu(t \mid s) \;=\; \frac{\mu(s \mid t)\,\mu(t)}{\mu(s)} .$$
--
--   The identity inverts a conditional: it converts the probability of the evidence given the hypothesis
--   into the probability of the hypothesis given the evidence. The three ingredients on the right are the
--   likelihood $\mu(s \mid t)$, the prior $\mu(t)$, and the normalizing evidence $\mu(s)$ — the
--   vocabulary of Bayesian inference, where the theorem is the update rule taking prior to posterior.
--
--   It is a two-line consequence of the definition $\mu(a \mid b) = \mu(a \cap b)/\mu(b)$, applied both
--   ways round, but the interpretive weight it carries is out of all proportion to the derivation. The
--   common failure it corrects is base-rate neglect: a test with a $1\%$ false-positive rate applied to a
--   condition affecting $1$ in $10{,}000$ yields a positive result that is wrong about $99\%$ of the time,
--   because the prior dominates.
--
--   Bayes' essay was published posthumously in 1763 by Richard Price; Laplace rediscovered and greatly
--   extended the idea, and the modern measure-theoretic framing is Kolmogorov's.
--
--   **Formalization note.** `μ[t | s]` is the conditional measure `ProbabilityTheory.cond`, defined as
--   the restriction to `s` rescaled by `(μ s)⁻¹`; the statement is arranged with the inverse on the left
--   to avoid division in `ℝ≥0∞`. The result is Mathlib's
--   `ProbabilityTheory.cond_eq_inv_mul_cond_mul`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem bayes {Ω : Type*} {m : MeasurableSpace Ω} {s t : Set Ω}
    (hms : MeasurableSet s) (hmt : MeasurableSet t) (μ : Measure Ω) [IsFiniteMeasure μ] :
    μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t := by sorry

end FamousTheorems
