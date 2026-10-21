-- Prove2me | Theorems.Thm_AccountingRules_Threshold_binary_reduction
-- name    : AccountingRules.Threshold.binary_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:42.231121+00:00
-- url     : https://prove2.me/theorems/d9e37a33-8e60-48d8-85f9-3aef584a038b
-- title:
--   Appendix A.1, p. 9 — reduction from posterior accounting rules to binary rules
-- statement:
--   Let $P$ satisfy the paper's standing prior and support assumptions, and let $\tau$ be any Bayes-plausible distribution over posteriors. There is a measurable binary rule $m:[\underline\theta,\overline\theta]\to[0,1]$ that satisfies both posterior mean constraints (A.1) and (A.2) and preserves the regulator's value:
--   $$\int V(\mu)\,d\tau(\mu)=\int\theta m(\theta)\,dP(\theta)+M\left(1-\int m(\theta)\,dP(\theta)\right).$$
--   This is the bridge from optimization over arbitrary accounting rules to the binary program used in Appendix A.1.
--
--   **Formalization Note** The measurable rule is defined on all real states and constrained pointwise to $[0,1]$; only its values on the support of $P$ affect the integrals. Equality of values represents the paper's claim that posteriors within each payoff segment can be combined.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, p. 9 (PDF 10), Appendix A.1, posterior-approach paragraph and (A.1)–(A.2)

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, p. 9: the posterior problem reduces to the binary program. -/
theorem binary_reduction (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (τ : Measure (Measure ℝ))
    (hτ : FinDisclosure.Threshold.IsBayesPlausible P τ) :
    ∃ m : ℝ → ℝ, IsRule m ∧ A1 P M B m ∧ A2 P M B m ∧
      value M B τ = objective P M m := by sorry

end AccountingRules.Threshold
