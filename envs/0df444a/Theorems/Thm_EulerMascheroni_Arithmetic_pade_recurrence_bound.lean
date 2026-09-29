-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_recurrence_bound
-- name    : EulerMascheroni.Arithmetic.pade_recurrence_bound
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:11:05.355699+00:00
-- url     : https://prove2.me/theorems/072e5a2f-0b19-4e25-81c5-df9295816f30
-- title:
--   An elementary factorial bound for the Euler Padé recurrence
-- statement:
--   Let $U_n\in\mathbb Z$ satisfy $|U_0|\le1$, $|U_1|\le4$ and
--
--   $$U_{n+2}=(2n+4)U_{n+1}-(n+1)^2U_n.$$
--
--   Then $|U_n|\le4^n n!$ for every $n\ge0$. This bound suffices after normalization by $(n!)^2$.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11). The normalization and algebraic-norm argument are an elementary derivation for this decomposition; the arithmetic division conjecture is not assumed in the unconditional lemmas.

import Mathlib
open Filter
open scoped Topology

theorem EulerMascheroni.Arithmetic.pade_recurrence_bound (U : ℕ → ℤ) (h0 : |U 0| ≤ 1) (h1 : |U 1| ≤ 4)
    (hU : ∀ n : ℕ, U (n+2) = (2*(n:ℤ)+4)*U (n+1) - ((n:ℤ)+1)^2*U n)
    (n : ℕ) : |U n| ≤ (4 : ℤ)^n * (n.factorial : ℤ) := by sorry
