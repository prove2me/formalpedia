-- Prove2me | Theorems.Thm_CollatzFrontier_chainCertificate_accepts
-- name    : CollatzFrontier.chainCertificate_accepts
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:58:17.935992+00:00
-- url     : https://prove2.me/theorems/a5df2493-ab51-482e-b8d0-e7133123a724
-- title:
--   Completeness of the executable Syracuse descent checker on canonical dyadic chains
-- statement:
--   Fix two sequences $a, b : \mathbb{N} \to \mathbb{N}$ (exponents and representatives) and a dyadic modulus budget $K$. `chainCertificate a b K k` packages the length-$k$ prefix of this data into the executable `DescentCertificate` format of `Def_collatzFrontierCertificate` (the coefficient at step $i$ is the exact remaining budget $3^i \cdot 2^{K - \sum_{j<i} a_j}$). This theorem is the completeness (acceptance) bridge between an abstract Syracuse-step chain and the executable checker `checkDescent`:
--   $$\mathrm{checkDescent}(\mathrm{chainCertificate}\ a\ b\ K\ k) = \mathrm{true}$$
--   whenever (i) the start representative $b_0$ is a positive odd number strictly below $2^K$ (so the family $b_0 + 2^K q$ is a canonical progression), (ii) every exponent $a_i$ for $i \le k$ is positive, (iii) the exact division identity $3 b_i + 1 = 2^{a_i} b_{i+1}$ holds through step $k$, (iv) every intermediate representative $b_{i+1}$ for $i < k$ is odd, (v) the cumulative exponent budget $\sum_{i \le k} a_i$ does not exceed $K$, and (vi) the representative strictly decreases ($b_{k+1} < b_0$).
--
--   **Role and reuse.** This is the single reusable checker-completeness engine behind both the linear-budget completeness theorem (`bounded_descent_generated`, which instantiates it with the factorization-derived exponent/representative sequence of an actual Syracuse orbit) and the adaptive-budget completeness equivalence (`eventual_descent_iff_certificate`, via the same instantiation). Packaging it as its own platform theorem removes the need to re-derive this ~60-line argument inside each of those two headline proofs.
--
--   **Formalization Note.** Transcribed verbatim from `CollatzFrontier.chainCertificate_accepts` in `lean/CollatzFrontier/CertificateCompleteness.lean`. All eight hypotheses are used in the proof; none were dropped.
-- source:
--   collatz-frontier (private repo), branch research/executable-coverage-20261002 @ 3835de1c8e7bf56d5632af07979d0fd2d580095c (stacks on research/certificate-density-20261002 @ 61e6b54c74e600c8c72fc2d271f5b4d11e9e8869 and main @ 4d656b9c9c5815305bd391f206c9d3e9587dd395); lean/CollatzFrontier/CertificateCompleteness.lean, theorem chainCertificate_accepts. Published here as a reusable intermediate lemma (original result of this contribution's packaging), cited by CollatzFrontier.bounded_descent_generated and CollatzFrontier.eventual_descent_iff_certificate.

import Definitions.Def_collatzFrontierCertificate

namespace CollatzFrontier

theorem chainCertificate_accepts (a b : ℕ → ℕ) (K k : ℕ)
    (hbpos : 0 < b 0) (hcanonical : b 0 < 2 ^ K) (hbodd : Odd (b 0))
    (hapos : ∀ i ≤ k, 0 < a i)
    (hstep : ∀ i ≤ k, 3 * b i + 1 = 2 ^ (a i) * b (i + 1))
    (hodd : ∀ i < k, Odd (b (i + 1)))
    (hbudget : (∑ i ∈ Finset.range (k + 1), a i) ≤ K)
    (hdesc : b (k + 1) < b 0) :
    checkDescent (chainCertificate a b K k) = true := by sorry

end CollatzFrontier
