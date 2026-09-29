-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_determinant_and_nonvanishing
-- name    : EulerMascheroni.Arithmetic.pade_determinant_and_nonvanishing
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:38:09.031035+00:00
-- url     : https://prove2.me/theorems/b7f69e92-2d00-4bcf-8196-16f3681f166d
-- title:
--   Factorial determinant and adjacent nonvanishing for the Euler Padé recurrence
-- statement:
--   Let integer sequences $P_n,Q_n$ satisfy
--
--   $$U_{n+2}=(2n+4)U_{n+1}-(n+1)^2U_n\quad(U=P,Q),\qquad Q_0P_1-Q_1P_0=1.$$
--
--   Then, for every $n\ge0$,
--
--   $$Q_nP_{n+1}-Q_{n+1}P_n=(n!)^2.$$
--
--   Consequently, for every real $a$, the adjacent linear forms $Q_na-P_n$ and $Q_{n+1}a-P_{n+1}$ cannot both vanish. This is the determinant-based nonvanishing ingredient of the Euler Padé method. No bound on the sizes of the linear forms is assumed or concluded.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eq. (11) and the nonvanishing argument following Eq. (10). The present theorem is an unconditional general recurrence formulation; its determinant formula follows by induction from the explicitly stated recurrence hypotheses.

import Mathlib

theorem EulerMascheroni.Arithmetic.pade_determinant_and_nonvanishing (P Q : ℕ → ℤ)
    (h0 : Q 0 * P 1 - Q 1 * P 0 = 1)
    (hP : ∀ n : ℕ, P (n+2) = (2*(n:ℤ)+4)*P (n+1) - ((n:ℤ)+1)^2*P n)
    (hQ : ∀ n : ℕ, Q (n+2) = (2*(n:ℤ)+4)*Q (n+1) - ((n:ℤ)+1)^2*Q n) :
    ∀ n : ℕ,
      Q n * P (n+1) - Q (n+1) * P n = (n.factorial : ℤ)^2 ∧
      ∀ a : ℝ, (Q n : ℝ)*a - (P n : ℝ) ≠ 0 ∨
        (Q (n+1) : ℝ)*a - (P (n+1) : ℝ) ≠ 0 := by sorry
