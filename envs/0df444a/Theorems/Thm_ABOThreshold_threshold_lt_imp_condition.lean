-- Prove2me | Theorems.Thm_ABOThreshold_threshold_lt_imp_condition
-- name    : ABOThreshold.threshold_lt_imp_condition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:35:28.3417+00:00
-- url     : https://prove2.me/theorems/7902e316-7ecc-431f-a119-4c9de45d23dc
-- title:
--   Below $\eta_c$ the threshold condition holds
-- statement:
--   Let $A$ be the maximal number of locations in a rectangle and let $k\ge 1$ be the number of faulty sub-rectangles a rectangle tolerates. The threshold for probabilistic noise is $\eta_c = \binom{A}{k+1}^{-1/k}$.
--
--   The assertion is that every error rate in the range $0<\eta<\eta_c$ satisfies the threshold condition
--
--   $$\binom{A}{k+1}\,\eta^{k+1} \;<\; \eta .$$
--
--   This is the sentence "it is easy to see that any $\eta<\eta_c$ satisfies the threshold condition" that follows Definition 20, and it is what licenses using the threshold condition throughout the recursive analysis whenever the error rate is below the threshold.
--
--   **Formalization Note** The paper prints $\eta_c$ with exponent $-k$; the exponent $-1/k$ is used here, since it is the one for which this statement is true and it is what solving the threshold condition gives.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, p. 51, Definitions 19 and 20 (eqs. 7.3, 7.4)

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem threshold_lt_imp_condition (A k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η)
    (hlt : η < thresholdProb A k) : ThresholdCondition A k η := by sorry

end ABOThreshold
