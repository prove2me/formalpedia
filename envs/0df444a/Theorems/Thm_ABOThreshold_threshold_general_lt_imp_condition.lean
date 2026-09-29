-- Prove2me | Theorems.Thm_ABOThreshold_threshold_general_lt_imp_condition
-- name    : ABOThreshold.threshold_general_lt_imp_condition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:41:59.866227+00:00
-- url     : https://prove2.me/theorems/a75e0d66-9f56-4482-a643-9d32c6e7bd00
-- title:
--   Below $\eta_c'$ the general-noise threshold condition holds
-- statement:
--   In the general noise model the noise operator at each location is only assumed to be within $\eta$ of the identity, and the analysis costs a factor of $2$ in the error rate and a factor of $e$ overall. The threshold condition for general noise (Definition 21) is
--
--   $$e\binom{A}{k+1}(2\eta)^{k+1} \;<\; 2\eta,$$
--
--   and the corresponding threshold (Definition 22) is $\eta_c' = \tfrac12\bigl(e\binom{A}{k+1}\bigr)^{-1/k}$, which is smaller than the threshold $\eta_c$ for probabilistic noise.
--
--   The assertion is that, for $k\ge1$, every error rate $0<\eta<\eta_c'$ satisfies the general-noise threshold condition.
--
--   **Formalization Note** As for the probabilistic threshold, the exponent is taken to be $-1/k$ rather than the $-k$ printed in equation 8.6.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, pp. 53-54, Definitions 21 and 22 (eqs. 8.5, 8.6)

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem threshold_general_lt_imp_condition (A k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η)
    (hlt : η < thresholdGeneral A k) : ThresholdConditionGeneral A k η := by sorry

end ABOThreshold
