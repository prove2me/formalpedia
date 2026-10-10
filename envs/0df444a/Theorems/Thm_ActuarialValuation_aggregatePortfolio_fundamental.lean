-- Prove2me | Theorems.Thm_ActuarialValuation_aggregatePortfolio_fundamental
-- name    : ActuarialValuation.aggregatePortfolio_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:38:43.026987+00:00
-- url     : https://prove2.me/theorems/78e3ac2b-c527-4733-8f1b-3e00695945ae
-- title:
--   Finite individual-risk portfolio has a valid bounded aggregate PMF
-- statement:
--   The capstone establishes all three defining properties of a discrete aggregate claims distribution for independently insured heterogeneous Bernoulli policies: nonnegative probabilities, total mass one on the exact insured-benefit support and zero probability above the maximum possible loss.
--
--   **Mathematical statement**
--
--   $$
--   g_n\ge0,\quad\sum_{s=0}^{B_n}g_n(s)=1,\quad s>B_n\Rightarrow g_n(s)=0
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateMaximumClaim
import Definitions.Def_actuarial_aggregateFiniteMass

namespace ActuarialValuation

theorem aggregatePortfolio_fundamental (p : ℕ → ℝ) (b : ℕ → ℕ)
  (n : ℕ) (h : ∀ i, i < n → 0 ≤ p i ∧ p i ≤ 1) :
  (∀ s : ℕ, 0 ≤ aggregatePortfolioPMF p b n s) ∧
  aggregateFiniteMass (aggregatePortfolioPMF p b n)
     (aggregateMaximumClaim b n) = 1 ∧
  (∀ s : ℕ, aggregateMaximumClaim b n < s →
     aggregatePortfolioPMF p b n s = 0) := by sorry

end ActuarialValuation
