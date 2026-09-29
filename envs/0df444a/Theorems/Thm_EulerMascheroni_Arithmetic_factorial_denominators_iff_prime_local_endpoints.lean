-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_factorial_denominators_iff_prime_local_endpoints
-- name    : EulerMascheroni.Arithmetic.factorial_denominators_iff_prime_local_endpoints
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:02:55.67938+00:00
-- url     : https://prove2.me/theorems/2df10f44-402f-440d-855d-720525cdabe3
-- title:
--   Prime-local endpoint criterion for exponential factorial-quotient denominators
-- statement:
--   For any real parameter $a$, the simultaneous exponential denominator condition for $q_k(a)=(a-\sum_{j<k}(-1)^j j!)/k!$ is equivalent to the following endpoint condition. There is $C\ge1$ such that for every $n$ one can choose a positive integer $D\le C^{n+1}$ for which, at every prime $p$, some integer $d$ with $p\nmid d$ makes $dDq_n(a)$ integral over $\mathbb Z$. Prime-local integrality first gives global endpoint integrality; the quotient recurrence then gives integrality of the whole prefix.
-- source:
--   Integral closedness and principal ideals over the integers; prime-local reformulation of the Euler factorial quotient arithmetic division conjecture. Compare Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjecture 2, and Matala-aho–Zudilin, https://arxiv.org/html/1703.02633, Section 2.

import Definitions.Def_eulerMascheroni_factorialQuotient
open EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.factorial_denominators_iff_prime_local_endpoints (a : ℝ) :
    ExponentialDenominators a ↔
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ∃ D : ℕ, 0 < D ∧ (D:ℝ) ≤ C^(n+1) ∧
      ∀ p : ℕ, p.Prime → ∃ d : ℤ, ¬(p:ℤ) ∣ d ∧
        IsIntegral ℤ ((d:ℝ)*((D:ℝ)*quotientCoeff a n)) := by sorry
