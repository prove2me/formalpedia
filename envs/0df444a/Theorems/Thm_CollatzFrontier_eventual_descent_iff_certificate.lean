-- Prove2me | Theorems.Thm_CollatzFrontier_eventual_descent_iff_certificate
-- name    : CollatzFrontier.eventual_descent_iff_certificate
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:58:25.599828+00:00
-- url     : https://prove2.me/theorems/63797e2f-629c-4467-a3d0-fa25ea7d184c
-- title:
--   Eventual Syracuse descent is equivalent to acceptance by an adaptive dyadic certificate
-- statement:
--   Let $n$ be a positive odd natural number. This theorem is the main completeness equivalence for the descent-certificate checker of `Def_collatzFrontierCertificate`:
--   $$(\exists t,\ \mathrm{syracuseStep}^{[t]}(n) < n) \iff \big(\exists K,\ \exists\, \mathrm{cert},\ \mathrm{cert.start.constant}=n \wedge \mathrm{cert.start.coefficient}=2^K \wedge \mathrm{checkDescent}(\mathrm{cert})=\mathrm{true}\big).$$
--   In words: $n$ eventually Syracuse-descends if and only if some dyadic certificate rooted at $n$ is accepted by the actual checker. The forward direction constructs an explicit accepted certificate (`chainCertificate`) from the actual orbit's 2-adic valuations once a descent time $t$ is known; the reverse direction is checker soundness: acceptance of any certificate rooted at $n$ genuinely forces a strict decrease after finitely many Syracuse steps. Both the modulus $K$ and the time witnessing descent are existentially quantified and may depend adaptively on $n$; this equivalence supplies no uniform bound on either.
--
--   **Role and reuse.** This is the foundational completeness statement underlying the entire certificate-checker program: it is the precise sense in which checking `checkDescent` on some certificate is equivalent to, not merely a sufficient condition for, eventual descent. The forward direction's construction reduces to the imported platform theorem `CollatzFrontier.chainCertificate_accepts`.
--
--   **Formalization Note.** Transcribed verbatim from `CollatzFrontier.eventual_descent_iff_certificate` in `lean/CollatzFrontier/CertificateCompleteness.lean` (on `main`). Both hypotheses (`hn`, `hodd`) are used in the proof; none were dropped.
-- source:
--   collatz-frontier (private repo), branch research/executable-coverage-20261002 @ 3835de1c8e7bf56d5632af07979d0fd2d580095c (stacks on research/certificate-density-20261002 @ 61e6b54c74e600c8c72fc2d271f5b4d11e9e8869 and main @ 4d656b9c9c5815305bd391f206c9d3e9587dd395); lean/CollatzFrontier/CertificateCompleteness.lean (main @ 4d656b9), theorem eventual_descent_iff_certificate.

import Definitions.Def_collatzFrontierCertificate

namespace CollatzFrontier

theorem eventual_descent_iff_certificate (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    (∃ t : ℕ, syracuseStep^[t] n < n) ↔
      ∃ K : ℕ, ∃ cert : DescentCertificate,
        cert.start.constant = n ∧ cert.start.coefficient = 2 ^ K ∧
        checkDescent cert = true := by sorry

end CollatzFrontier
