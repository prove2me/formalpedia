-- Prove2me | Theorems.Thm_CollatzFrontier_bounded_checker_asymptotic_coverage
-- name    : CollatzFrontier.bounded_checker_asymptotic_coverage
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T18:31:40.94412+00:00
-- url     : https://prove2.me/theorems/003f5af2-2109-4402-a79c-162cc14395a1
-- title:
--   Asymptotic coverage of the executable automatic descent-certificate checker tends to one
-- statement:
--   This theorem converts the explicit failure-rate bound of `CollatzFrontier.automatic_certificate_failure_bound` into an asymptotic coverage guarantee for the actual executable checker:
--   $$\forall \varepsilon>0\ \exists m\ge 2\ \forall R\ge 2^{24m}:\ \frac{\mathrm{automaticCertificateFailureCount}(R,m)}{R} < \varepsilon.$$
--   For every target accuracy $\varepsilon>0$ there is a fixed accuracy parameter $m \ge 2$, chosen before the sample size $R$ varies, such that for every sufficiently large $R$ the failure fraction of one finite, fully specified checker call is below $\varepsilon$. Only the step count $4m$ is fixed across $R$: the ambient bit-width $L = \lceil \log_2(2R) \rceil$, and hence the generator's fuel and modulus exponent $L+8m$, grow with $R$ — each test instance still runs in finite, explicitly bounded time for its own $R$, but there is no single fixed-size test reused unchanged for every $R$. This family of genuinely finite tests achieves arbitrarily high asymptotic coverage; it does not claim that any single fixed bounded-time test has density one, that every input passes, or that rejection proves an input never descends.
--
--   **Role and reuse.** A direct limiting corollary of `automatic_certificate_failure_bound`, included because the three geometric error rates in that bound are each below $1$, so their sum tends to $0$ by elementary analysis — a cheap but informative strengthening from "explicit bound" to "coverage tends to one".
--
--   **Formalization Note.** Transcribed verbatim from `CollatzFrontier.bounded_checker_asymptotic_coverage` in `lean/CollatzFrontier/ExecutableCertificateCoverage.lean`. This statement has no external hypotheses to drop.
-- source:
--   collatz-frontier (private repo), branch research/executable-coverage-20261002 @ 3835de1c8e7bf56d5632af07979d0fd2d580095c (stacks on research/certificate-density-20261002 @ 61e6b54c74e600c8c72fc2d271f5b4d11e9e8869 and main @ 4d656b9c9c5815305bd391f206c9d3e9587dd395); lean/CollatzFrontier/ExecutableCertificateCoverage.lean, theorem bounded_checker_asymptotic_coverage.

import Definitions.Def_collatzFrontierCoverage
import Mathlib.Data.Real.Basic

namespace CollatzFrontier

theorem bounded_checker_asymptotic_coverage :
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 2 ≤ m ∧ ∀ R : ℕ, 2 ^ (24 * m) ≤ R →
      (automaticCertificateFailureCount R m : ℝ) / R < ε := by sorry

end CollatzFrontier
