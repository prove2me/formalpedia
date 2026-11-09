-- Prove2me | Theorems.Thm_BQPNotInIP_OracleSep_fact_4_0_1
-- name    : BQPNotInIP.OracleSep.fact_4_0_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:52:49.983993+00:00
-- url     : https://prove2.me/theorems/24bfdcf9-141e-4aef-bf6a-8c9ee6834ea0
-- title:
--   Fact 4.0.1 — Gaussian sign identity
-- statement:
--   Let $X,Y$ be any jointly Gaussian centered real random variables with strictly positive variances, and let
--   $$
--   \rho=\frac{\operatorname{Cov}(X,Y)}{\sqrt{\operatorname{Var}(X)\operatorname{Var}(Y)}}.
--   $$
--   Then
--   $$
--   \mathbb E[\operatorname{sgn}(X)\operatorname{sgn}(Y)]=\frac2\pi\arcsin\rho.
--   $$
--   The formal statement uses the canonical centered Gaussian law with an arbitrary positive-semidefinite two-by-two covariance matrix and positive diagonal entries. It covers perfectly correlated and anticorrelated pairs as well as nonsingular joint laws. This identity controls the probability of a sign change in the final step of Corollary 6.6.
--
--   Differences from the source:
--   - encoding: an arbitrary centered jointly Gaussian pair with positive variances → the centered bivariate Gaussian law with arbitrary positive-semidefinite covariance and positive diagonal entries; reason: every such pair has this joint law; no unit-variance or independent-coordinate representation is assumed
--   - encoding: Gaussian sign rounding → Real.sign, with sign zero equal to zero; reason: every rounded coordinate has positive variance, so zero has probability zero
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), Fact 4.0.1, PDF p. 11 (printed p. 9). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=11

import Definitions.Def_BQPNotInIP_OracleSep_Analysis

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace BQPNotInIP.OracleSep

theorem fact_4_0_1 (cov : Matrix (Fin 2) (Fin 2) ℝ)
    (hcov : cov.PosSemidef) (hX : 0 < cov 0 0) (hY : 0 < cov 1 1) :
    (∫ x, Real.sign (x 0) * Real.sign (x 1) ∂(gaussian 2 cov)) =
      (2/Real.pi) * Real.arcsin (cov 0 1 / Real.sqrt (cov 0 0 * cov 1 1)) := by sorry

end BQPNotInIP.OracleSep
