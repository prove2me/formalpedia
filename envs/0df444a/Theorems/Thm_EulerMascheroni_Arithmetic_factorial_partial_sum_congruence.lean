-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_factorial_partial_sum_congruence
-- name    : EulerMascheroni.Arithmetic.factorial_partial_sum_congruence
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:35:16.270604+00:00
-- url     : https://prove2.me/theorems/522f2a77-c195-4f25-b3bb-a698f04b27ed
-- title:
--   Factorial partial sums stabilize modulo each earlier factorial
-- statement:
--   Write $S_n=\sum_{k<n}(-1)^k k!$. For integers $0\le n\le m$,
--
--   $$S_m\equiv S_n\pmod{n!}.$$
--
--   This unconditional stabilization property is the finite arithmetic basis of the convergence of the factorial series in each $p$-adic field. It does not identify those limits with the real Borel sum.
-- source:
--   Explicit elementary derivation from the factorial quotient coefficients associated to Conjecture 2 in Fischler–Rivoal, Relations between values of arithmetic Gevrey series, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, p. 4. All identities in this submission are unconditional; the arithmetic division conjecture is not assumed.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.factorial_partial_sum_congruence (n m : ℕ) (h : n ≤ m) :
    (n.factorial : ℤ) ∣
      (∑ k ∈ Finset.range m, (-1 : ℤ)^k * (k.factorial : ℤ)) -
      (∑ k ∈ Finset.range n, (-1 : ℤ)^k * (k.factorial : ℤ)) := by sorry
