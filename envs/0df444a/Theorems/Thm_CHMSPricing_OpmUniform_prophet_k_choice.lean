-- Prove2me | Theorems.Thm_CHMSPricing_OpmUniform_prophet_k_choice
-- name    : CHMSPricing.OpmUniform.prophet_k_choice
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:37:50.561776+00:00
-- url     : https://prove2.me/theorems/6cbb5506-d35a-4582-bf43-f84469b62000
-- title:
--   Theorem 24, p. 18 — k-choice prophet inequality: a threshold rule collects half of the k largest values
-- statement:
--   Let $X_1, \dots, X_n$ be independent, nonnegative, integrable random variables, let $1 \le k \le n$, and let $X_{(1)} \ge \dots \ge X_{(n)}$ be their order statistics. Let $a^*$ and $b^*$ be the solutions of
--   $$a = \sum_{i=1}^k \mathbb E\big(X_{(i)} - a/k\big)^+, \qquad b = \sum_{i=1}^n \mathbb E\big(X_i - b/k\big)^+ .$$
--   For a threshold $c$, let $t_1(c), \dots, t_k(c)$ be the indices chosen by the threshold stopping rule: $t_i(c)$ is the lesser of $n-k+i$ and the $i$-th smallest index $j$ with $X_j \ge c$ (or $n-k+i$ when there is no such index). If $a^* \le k c \le b^*$, then
--   $$\sum_{i=1}^k \mathbb E\big[X_{(i)}\big] \le 2 \sum_{i=1}^k \mathbb E\big[X_{t_i(c)}\big].$$
--
--   A gambler who sees the values in order and may keep $k$ of them, using one fixed threshold, expects at least half of what a prophet who keeps the $k$ largest values expects. This extends Samuel-Cahn's single-choice prophet inequality to $k$ choices, and is the probabilistic core of Theorem 10.
--
--   **Formalization Note** Indices are 0-based in Lean (`orderStat` and `threshIdx`, see the Prophet definition). The rule includes the page's forced picks $t_i(c) = n-k+i$, which the gambler takes even when they are below $c$. $a^*$ and $b^*$ are characterised by their equations. Nonnegativity is almost sure; the variables are measurable and mutually independent.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 18, App. D.2, Theorem 24

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Prophet

namespace CHMSPricing.OpmUniform

open MeasureTheory ProbabilityTheory

theorem prophet_k_choice {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω) (hXint : ∀ i, Integrable (X i) P) (a b c : ℝ)
    (ha : a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P)
    (hb : b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P)
    (hac : a ≤ k * c) (hcb : k * c ≤ b) :
    ∑ i : Fin k, ∫ ω, orderStat (fun j => X j ω) i ∂P ≤
      2 * ∑ i : Fin k, ∫ ω, X (threshIdx hkn (fun j => X j ω) c i) ω ∂P := by sorry

end CHMSPricing.OpmUniform
