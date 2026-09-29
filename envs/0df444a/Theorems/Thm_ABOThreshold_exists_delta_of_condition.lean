-- Prove2me | Theorems.Thm_ABOThreshold_exists_delta_of_condition
-- name    : ABOThreshold.exists_delta_of_condition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:40:04.685997+00:00
-- url     : https://prove2.me/theorems/c08e3f23-55e2-4ae1-aa63-a0eb5a4e95f3
-- title:
--   Existence of the exponent gap $\delta$ (eq. 7.5)
-- statement:
--   Let $0<\eta<1$ be an error rate satisfying the threshold condition $\binom{A}{k+1}\eta^{k+1}<\eta$.
--
--   The assertion is that the strict inequality leaves room for a positive exponent gap: there exists $\delta>0$ with
--
--   $$\binom{A}{k+1}\,\eta^{k+1} \;<\; \eta^{\,1+\delta}.$$
--
--   This is equation 7.5 of the paper. The number $\delta$ is what turns one level of concatenation into a genuine improvement of the effective error rate, and iterating it $r$ times is what produces the doubly exponential decay $\eta^{(1+\delta)^r}$ of Lemma 10.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, p. 52, proof of Lemma 10, eq. (7.5)

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem exists_delta_of_condition (A k : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hc : ThresholdCondition A k η) :
    ∃ δ : ℝ, 0 < δ ∧ (A.choose (k + 1) : ℝ) * η ^ (k + 1) < η ^ (1 + δ) := by sorry

end ABOThreshold
