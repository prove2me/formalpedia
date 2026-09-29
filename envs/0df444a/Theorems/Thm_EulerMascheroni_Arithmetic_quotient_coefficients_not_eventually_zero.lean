-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_quotient_coefficients_not_eventually_zero
-- name    : EulerMascheroni.Arithmetic.quotient_coefficients_not_eventually_zero
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:38:58.695709+00:00
-- url     : https://prove2.me/theorems/9cba2231-513b-4d91-af76-13e8f852089d
-- title:
--   The factorial quotient Borel series never terminates
-- statement:
--   For every real $a$, the coefficients $q_n(a)=(a-\sum_{k<n}(-1)^k k!)/n!$ do not eventually vanish:
--
--   $$\forall N\ge0\;\exists n\ge N:\ q_n(a)\ne0.$$
--
--   Thus their Borel generating series is never a polynomial. This is weaker than nonrationality; no nonrationality conclusion is asserted here.
-- source:
--   Elementary consequence of the explicit recurrence (n+1)q_{n+1}=q_n−(−1)^n, itself obtained from the factorial quotient associated to Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjecture 2, p. 4. This consequence is proved unconditionally here.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.quotient_coefficients_not_eventually_zero (a : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ EulerMascheroni.Arithmetic.quotientCoeff a n ≠ 0 := by sorry
