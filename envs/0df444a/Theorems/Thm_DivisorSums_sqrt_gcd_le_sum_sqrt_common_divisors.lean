-- Prove2me | Theorems.Thm_DivisorSums_sqrt_gcd_le_sum_sqrt_common_divisors
-- name    : DivisorSums.sqrt_gcd_le_sum_sqrt_common_divisors
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:52.697415+00:00
-- url     : https://prove2.me/theorems/0f65e302-85d6-4cc7-bbc6-889bb216207b
-- title:
--   $\sqrt{\gcd}$ is bounded by a sum over common divisors
-- statement:
--   **The square root of a gcd is dominated by the sum over all common divisors.**
--
--   For $n \ne 0$ and any $m$,
--
--   $$\sqrt{\gcd(n,m)} \;\le\; \sum_{\substack{d \mid n \\ d \mid m}} \sqrt{d} .$$
--
--   The greatest common divisor is itself one of the common divisors of $n$ and $m$ — it divides
--   $n$, so it belongs to `n.divisors`, and it divides $m$, so it survives the filter. Its
--   contribution $\sqrt{\gcd(n,m)}$ is therefore one term of a sum whose every term is
--   non-negative, which gives the bound.
--
--   The value of the inequality is that it **linearises** the gcd. A weight $\sqrt{\gcd(n,m)}$
--   depends on $n$ and $m$ jointly and resists interchange of summation; replacing it by a sum over
--   common divisors turns it into a double sum whose inner variable $d$ can be summed first. That
--   manoeuvre is routine in bounding Kloosterman-type sums and in sieve estimates where gcd weights
--   appear after grouping residues by their common factor with the modulus.
--
--   **Formalization note.** `n.divisors` is empty when $n = 0$, which is why $n \ne 0$ is assumed;
--   the filter selects those divisors of $n$ that also divide $m$.
-- source:
--   Elementary; the linearisation step in gcd-weighted divisor estimates, cf. Iwaniec & Kowalski, *Analytic Number Theory*, §1.4. Lean proof extracted from `Salt/Weil/GcdDivisorSum.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorSums

theorem sqrt_gcd_le_sum_sqrt_common_divisors (n m : ℕ) (hn : n ≠ 0) :
    Real.sqrt (Nat.gcd n m) ≤ ∑ d ∈ n.divisors.filter (· ∣ m), Real.sqrt d := by sorry

end DivisorSums
