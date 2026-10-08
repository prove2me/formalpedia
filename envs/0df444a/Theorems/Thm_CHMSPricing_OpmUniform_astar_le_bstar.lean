-- Prove2me | Theorems.Thm_CHMSPricing_OpmUniform_astar_le_bstar
-- name    : CHMSPricing.OpmUniform.astar_le_bstar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:37:38.371044+00:00
-- url     : https://prove2.me/theorems/32e2c604-0142-48cd-9469-76f120ba708b
-- title:
--   App. D.2, p. 18 — the solution $a^*$ of the prophet's equation is at most the solution $b^*$ of the gambler's
-- statement:
--   Let $X_1, \dots, X_n$ be independent, nonnegative, integrable random variables on a probability space, let $1 \le k \le n$, and let $X_{(1)} \ge \dots \ge X_{(n)}$ be their order statistics. If $a$ and $b$ are real numbers with
--   $$a = \sum_{i=1}^k \mathbb E\big(X_{(i)} - a/k\big)^+ \qquad\text{and}\qquad b = \sum_{i=1}^n \mathbb E\big(X_i - b/k\big)^+ ,$$
--   where $(x)^+ = \max(0,x)$, then
--   $$a \le b .$$
--
--   Hence the interval of thresholds $c$ with $a^* \le k c \le b^*$ in Theorem 24 is nonempty.
--
--   **Formalization Note** $a$ and $b$ are characterised by their equations (which have unique solutions), not defined through an infimum. The variables are mutually independent, as in the page's setting. Order statistics are counted with multiplicity.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 18, App. D.2, the claim a* ≤ b*

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Prophet

namespace CHMSPricing.OpmUniform

open MeasureTheory ProbabilityTheory

theorem astar_le_bstar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hXint : ∀ i, Integrable (X i) P) (a b : ℝ)
    (ha : a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P)
    (hb : b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P) :
    a ≤ b := by sorry

end CHMSPricing.OpmUniform
