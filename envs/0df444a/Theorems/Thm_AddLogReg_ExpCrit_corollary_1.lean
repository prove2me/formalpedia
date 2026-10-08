-- Prove2me | Theorems.Thm_AddLogReg_ExpCrit_corollary_1
-- name    : AddLogReg.ExpCrit.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:22.711989+00:00
-- url     : https://prove2.me/theorems/113e1093-85b9-49a7-a76a-16aab3e7437a
-- title:
--   Corollary 1, p. 346 — on a region where F is constant, the average of e^{−y_i c} is minimized at c = ½ log(n₊/n₋), matching the sample proportions
-- statement:
--   Let $y_1, \dots, y_n \in \{-1, 1\}$ be the labels of the observations in a region of feature space on which $F$ takes a constant value $c$ (for example a terminal node of a decision tree), and suppose both labels occur. Let $n_+$ and $n_-$ be the numbers of labels equal to $1$ and $-1$, and put
--   $$c^\star = \tfrac12 \log \frac{n_+}{n_-}.$$
--   Then
--
--   1. $c^\star$ minimizes the average exponential criterion over the region: for every real $c$,
--   $$\frac1n \sum_{i=1}^n e^{-y_i c^\star} \le \frac1n \sum_{i=1}^n e^{-y_i c};$$
--   2. the sample proportions are given by the symmetric logistic transform of $c^\star$:
--   $$\frac{n_+}{n} = \frac{e^{c^\star}}{e^{-c^\star} + e^{c^\star}}, \qquad \frac{n_-}{n} = \frac{e^{-c^\star}}{e^{-c^\star} + e^{c^\star}}.$$
--
--   This is the sample version of Lemma 1: replacing the expectation by averages over a region gives the same minimizer with sample proportions in place of conditional probabilities. It is what the data versions of the boosting algorithms compute in each terminal node.
--
--   **Formalization Note** The averages are written with the factor $1/n$, as in the corollary's "averages". The requirement that both labels occur is the sample counterpart of $0 < P(y = 1 \mid x) < 1$: without it the logarithm is of $0$ or a division by $0$, and no minimizer exists.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 346, Corollary 1

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.ExpCrit

/-- Corollary 1 (p. 346): with `E` replaced by the average over a region where `F` is a
constant `c` (labels `y_1, …, y_n`, both classes present), the average of `e^{−y_i c}` is
minimized at `c = ½ log(n₊/n₋)`, and the sample proportions of `y = 1` and `y = −1` are
`e^{c}/(e^{−c} + e^{c})` and `e^{−c}/(e^{−c} + e^{c})`. -/
theorem corollary_1 (n : ℕ) (y : Fin n → Bool) (hpos : ∃ i, y i = true)
    (hneg : ∃ i, y i = false) :
    let npos : ℕ := (Finset.univ.filter (fun i => y i = true)).card
    let nneg : ℕ := (Finset.univ.filter (fun i => y i = false)).card
    let c : ℝ := (1 / 2) * Real.log ((npos : ℝ) / nneg)
    (∀ c' : ℝ, (1 / (n : ℝ)) * ∑ i, Real.exp (-(sgn (y i) * c)) ≤
        (1 / (n : ℝ)) * ∑ i, Real.exp (-(sgn (y i) * c'))) ∧
    (npos : ℝ) / n = Real.exp c / (Real.exp (-c) + Real.exp c) ∧
    (nneg : ℝ) / n = Real.exp (-c) / (Real.exp (-c) + Real.exp c) := by sorry

end AddLogReg.ExpCrit
