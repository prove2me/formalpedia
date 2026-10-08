-- Prove2me | Theorems.Thm_CollatzFrontier_bounded_descent_generated
-- name    : CollatzFrontier.bounded_descent_generated
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:58:22.452411+00:00
-- url     : https://prove2.me/theorems/9fa112f4-9f0e-4a99-b490-7b32d3a2f43a
-- title:
--   Linear-budget completeness of the generated Syracuse descent certificate
-- statement:
--   Let $n$ be a positive odd natural number with $n < 2^L$ (so $L$ bits suffice to describe $n$), and suppose the Syracuse map descends at time $t$: $\mathrm{syracuseStep}^{[t]}(n) < n$ (iterating the accelerated map $\mathrm{syracuseStep}(n) = \mathrm{ordCompl}_2(3n+1)$ $t$ times drops below $n$). This theorem shows that the executable generator `candidateCertificate` of `Def_collatzFrontierCertificate` — which guesses each division's exponent by bounded trial division, capped by an explicit `fuel` parameter — already succeeds at the uniform, linear budget $\mathrm{fuel} = \text{modulus exponent} = L + 2t$:
--   $$\mathrm{checkDescent}\big(\mathrm{candidateCertificate}\ (L+2t)\ (t-1)\ n\ 2^{L+2t}\big) = \mathrm{true}.$$
--   In words: both the amount of trial division the generator needs, and the size of the certified residue class, scale only linearly in the input's bit-width $L$ and the number of descent steps $t$ — not merely as some unspecified (adaptively large) budget.
--
--   **Role and reuse.** This is the key uniform-budget estimate behind the explicit failure-rate bound (`automatic_certificate_failure_bound`), which calls it directly on every input it certifies as a bounded descent. Its proof reduces to the checker-completeness platform theorem `CollatzFrontier.chainCertificate_accepts`, plus an explicit estimate (`syracuse_total_valuation_budget`) on how large the cumulative 2-adic valuation of a Syracuse orbit's $3x+1$ numerators can be relative to the orbit's own linear growth bound.
--
--   **Formalization Note.** Transcribed verbatim from `CollatzFrontier.bounded_descent_generated` in `lean/CollatzFrontier/ExplicitCertificate.lean`. All four hypotheses (`hn`, `hodd`, `hsize`, `hdesc`) are used in the proof; none were dropped. No reference to the unproved joint-law proposition `SyracuseJointGeometricBound` ("M46") occurs anywhere in the statement or proof.
-- source:
--   collatz-frontier (private repo), branch research/executable-coverage-20261002 @ 3835de1c8e7bf56d5632af07979d0fd2d580095c (stacks on research/certificate-density-20261002 @ 61e6b54c74e600c8c72fc2d271f5b4d11e9e8869 and main @ 4d656b9c9c5815305bd391f206c9d3e9587dd395); lean/CollatzFrontier/ExplicitCertificate.lean, theorem bounded_descent_generated.

import Definitions.Def_collatzFrontierCertificate

namespace CollatzFrontier

theorem bounded_descent_generated (n L t : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hsize : n < 2 ^ L) (hdesc : syracuseStep^[t] n < n) :
    checkDescent (candidateCertificate (L + 2 * t) (t - 1) n
      (2 ^ (L + 2 * t))) = true := by sorry

end CollatzFrontier
