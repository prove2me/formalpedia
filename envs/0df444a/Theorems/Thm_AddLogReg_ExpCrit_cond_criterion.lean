-- Prove2me | Theorems.Thm_AddLogReg_ExpCrit_cond_criterion
-- name    : AddLogReg.ExpCrit.cond_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:50.853091+00:00
-- url     : https://prove2.me/theorems/708a808b-7d02-4a41-872c-7ad5160b2498
-- title:
--   §4.1, p. 345, proof of Lemma 1 — E(e^{−yF(x)}|x) = P(y=1|x)e^{−F(x)} + P(y=−1|x)e^{F(x)}, and J(F) = E_x[E(e^{−yF(x)}|x)]
-- statement:
--   Let $\nu$ be the joint law of $(x, y)$ on $X \times \{-1, 1\}$, with marginal $\nu_X$ on $X$, and let $P(y = \pm 1 \mid x)$ be the conditional class probabilities. Then:
--
--   1. for every $x \in X$ and every real $t$, the conditional exponential criterion at $F(x) = t$ is
--   $$E\big(e^{-yt} \mid x\big) = P(y = 1 \mid x)\, e^{-t} + P(y = -1 \mid x)\, e^{t};$$
--   2. for every measurable $F : X \to \mathbb R$, the exponential criterion $J(F) = E(e^{-yF(x)})$ is the $\nu_X$-expectation of the conditional criterion:
--   $$J(F) = \int_X E\big(e^{-yF(x)} \mid x\big)\, d\nu_X(x).$$
--
--   This is the first display of the proof of Lemma 1, together with the reduction "it is sufficient to minimize the criterion conditional on $x$": the joint minimization of $J$ splits into one scalar minimization for each $x$.
--
--   **Formalization Note** Both sides of item 2 are lower Lebesgue integrals in $[0, \infty]$; the conditional criterion is a finite nonnegative real converted with `ENNReal.ofReal`. Item 1 holds at every $x$, since the conditional kernel is a probability measure at every point.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 345, §4.1, proof of Lemma 1, first display

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.ExpCrit

/-- Proof of Lemma 1, first display (p. 345): `E(e^{−yF(x)}|x) = P(y = 1|x)e^{−F(x)} +
P(y = −1|x)e^{F(x)}`, and the joint criterion is the expectation over `x` of the conditional one. -/
theorem cond_criterion {X : Type*} [MeasurableSpace X] (ν : Measure (X × Bool))
    [IsProbabilityMeasure ν] :
    (∀ (x : X) (t : ℝ),
      condCrit ν x t = condProb ν true x * Real.exp (-t) + condProb ν false x * Real.exp t) ∧
    (∀ F : X → ℝ, Measurable F →
      J ν F = ∫⁻ x, ENNReal.ofReal (condCrit ν x (F x)) ∂ν.fst) := by sorry

end AddLogReg.ExpCrit
