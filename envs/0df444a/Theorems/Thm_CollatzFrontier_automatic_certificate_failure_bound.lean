-- Prove2me | Theorems.Thm_CollatzFrontier_automatic_certificate_failure_bound
-- name    : CollatzFrontier.automatic_certificate_failure_bound
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T18:31:37.230287+00:00
-- url     : https://prove2.me/theorems/a0f44624-1f83-48f3-9739-49baddba4148
-- title:
--   Explicit failure-rate bound for the executable automatic Syracuse descent-certificate checker
-- statement:
--   Fix an accuracy parameter $m \ge 2$ and a sample size $R$ with $2^{24m} \le R$. Recall `automaticCertificateFailureCount R m` (from `Def_collatzFrontierCoverage`): among the first $R$ positive odd integers, the number rejected by one fully specified, finite call to the actual executable checker (`boundedCertificateTest`, at $4m$ descent steps and an automatically computed ambient bit-width). This theorem gives an explicit, fully rational upper bound on the resulting failure fraction:
--   $$\frac{\mathrm{automaticCertificateFailureCount}(R,m)}{R} \le \left(\frac{81}{16777216}\right)^{m} + \left(\frac{16384}{16875}\right)^{m} + \left(\frac{1}{131072}\right)^{m}.$$
--   For each fixed $m$ this bounds the failure fraction of the accuracy-$m$ test; the bound is about $0.943$ at $m=2$ (valid once $R \ge 2^{48}$) and tends to $0$ as $m \to \infty$, each $m$ being a different finite test. The decay is slow (middle rate $\approx 0.971^{m}$). The result is unconditional: it does not assume the joint-law proposition `SyracuseJointGeometricBound` ("M46") used by an earlier conditional version.
--
--   **Role and reuse.** This is the headline quantitative coverage/completeness result for the actual executable checker: it is an unconditional, fully explicit accuracy/sample-size trade-off for a genuinely finite, machine-checkable test, as opposed to an existential membership predicate. Its proof reduces the checker-acceptance step to the imported platform theorem `CollatzFrontier.bounded_descent_generated`.
--
--   **Formalization Note.** Transcribed verbatim from `CollatzFrontier.automatic_certificate_failure_bound` in `lean/CollatzFrontier/ExecutableCertificateCoverage.lean`. Both hypotheses (`hm`, `hlarge`) are used in the proof; none were dropped.
-- source:
--   collatz-frontier (private repo), branch research/executable-coverage-20261002 @ 3835de1c8e7bf56d5632af07979d0fd2d580095c (stacks on research/certificate-density-20261002 @ 61e6b54c74e600c8c72fc2d271f5b4d11e9e8869 and main @ 4d656b9c9c5815305bd391f206c9d3e9587dd395); lean/CollatzFrontier/ExecutableCertificateCoverage.lean, theorem automatic_certificate_failure_bound. Improves on the conditional density estimate of CollatzFrontier.certifiable_odd_density_one_of_source_joint (lean/CollatzFrontier/CertificateDensity.lean) by removing its SyracuseJointGeometricBound ("M46") hypothesis via direct cylinder counting, and by replacing the adaptive-budget predicate Certifiable with the genuinely executable automaticCertificateFailureCount.

import Definitions.Def_collatzFrontierCoverage
import Mathlib.Data.Real.Basic

namespace CollatzFrontier

theorem automatic_certificate_failure_bound (R m : ℕ) (hm : 2 ≤ m)
    (hlarge : 2 ^ (24 * m) ≤ R) :
    (automaticCertificateFailureCount R m : ℝ) / R ≤
      (81 / 16777216 : ℝ) ^ m + (16384 / 16875 : ℝ) ^ m + (1 / 131072 : ℝ) ^ m := by sorry

end CollatzFrontier
