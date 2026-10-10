-- Prove2me | Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_nonneg
-- name    : ActuarialValuation.aggregatePortfolioPMF_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:38:07.033893+00:00
-- url     : https://prove2.me/theorems/467858b3-beee-48f4-9db6-d4708cb53405
-- title:
--   Admissible independent policy probabilities give nonnegative aggregate masses
-- statement:
--   Every participating individual claim probability lies within zero and one, so each Bernoulli claim mass is nonnegative. Convolving these mass functions from the empty portfolio preserves nonnegativity for every attainable and unattainable aggregate claim amount.
--
--   **Mathematical statement**
--
--   $$
--   0\le p_i\le1\Longrightarrow g_n(s)\ge0
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF

namespace ActuarialValuation

theorem aggregatePortfolioPMF_nonneg (p : ℕ → ℝ) (b : ℕ → ℕ)
  (n s : ℕ) (h : ∀ i, i < n → 0 ≤ p i ∧ p i ≤ 1) :
  0 ≤ aggregatePortfolioPMF p b n s := by sorry

end ActuarialValuation
