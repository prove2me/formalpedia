-- Prove2me | Theorems.Thm_CHMSPricing_OpmUniform_astar_bstar_existsUnique
-- name    : CHMSPricing.OpmUniform.astar_bstar_existsUnique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:37:29.431965+00:00
-- url     : https://prove2.me/theorems/6bdc38b7-3744-43ba-bf3d-c8c9c3151c47
-- title:
--   App. D.2, p. 18 — the equations for $a^*$ and $b^*$ have unique solutions
-- statement:
--   Let $X_1, \dots, X_n$ be independent, nonnegative, integrable random variables on a probability space, let $1 \le k \le n$, and let $X_{(1)} \ge \dots \ge X_{(n)}$ be their order statistics. Writing $(x)^+ = \max(0, x)$, each of the equations
--   $$a = \sum_{i=1}^k \mathbb E\big(X_{(i)} - a/k\big)^+ \qquad\text{and}\qquad b = \sum_{i=1}^n \mathbb E\big(X_i - b/k\big)^+$$
--   has exactly one real solution. The solutions are called $a^*$ and $b^*$.
--
--   The two numbers bracket the admissible thresholds of the $k$-choice prophet inequality (Theorem 24): any $c$ with $a^* \le kc \le b^*$ works.
--
--   **Formalization Note** The variables are mutually independent, as in the page's setting (the statement does not use it). Nonnegativity is almost sure.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 18, App. D.2, the sentence defining a* and b*

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Prophet

namespace CHMSPricing.OpmUniform

open MeasureTheory ProbabilityTheory

theorem astar_bstar_existsUnique {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hXint : ∀ i, Integrable (X i) P) :
    (∃! a : ℝ, a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P) ∧
    (∃! b : ℝ, b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P) := by sorry

end CHMSPricing.OpmUniform
