-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_rational_endpoint_integrality_iff_prime_powers
-- name    : EulerMascheroni.Arithmetic.rational_endpoint_integrality_iff_prime_powers
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:02:53.570875+00:00
-- url     : https://prove2.me/theorems/d20453d3-ed1c-44f3-a585-bb37f6230d54
-- title:
--   Prime-power divisibility test for rational factorial-quotient integrality
-- statement:
--   For integers $A,B$ with $B\ne0$, let $S_m=\sum_{j<m}(-1)^j j!$. The number $Dq_m(A/B)$ is integral over $\mathbb Z$ if and only if every prime power dividing $Bm!$ also divides $D(A-BS_m)$. This separates the exact rational endpoint condition into prime-power tests; only primes dividing the denominator need be considered.
-- source:
--   Integral closedness and principal ideals over the integers; prime-local reformulation of the Euler factorial quotient arithmetic division conjecture. Compare Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjecture 2, and Matala-aho–Zudilin, https://arxiv.org/html/1703.02633, Section 2.

import Definitions.Def_eulerMascheroni_factorialQuotient
open EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.rational_endpoint_integrality_iff_prime_powers (A B : ℤ) (hB : B ≠ 0) (D m : ℕ) :
    IsIntegral ℤ ((D:ℝ)*quotientCoeff ((A:ℝ)/(B:ℝ)) m) ↔
      ∀ p k : ℕ, p.Prime → (p^k:ℤ) ∣ B*(m.factorial:ℤ) →
        (p^k:ℤ) ∣ (D:ℤ)*(A-B*∑ j ∈ Finset.range m, (-1:ℤ)^j*j.factorial) := by sorry
