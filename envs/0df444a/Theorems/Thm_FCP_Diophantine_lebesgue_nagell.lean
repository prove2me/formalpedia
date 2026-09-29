-- Prove2me | Theorems.Thm_FCP_Diophantine_lebesgue_nagell
-- name    : FCP.Diophantine.lebesgue_nagell
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:31:36.73311+00:00
-- url     : https://prove2.me/theorems/38e0bcb1-e23a-42c0-beeb-29356f0c3d7d
-- title:
--   Lebesgue--Nagell equation $x^2 - 2 = y^p$
-- statement:
--   **The Lebesgue--Nagell equation.** For every odd prime $p$, the only integer solutions of
--   $$x^2 - 2 = y^{p}$$
--   are $(x, y) = (\pm 1, -1)$. The two exhibited pairs are solutions for every odd $p$, since $1 - 2 = -1 = (-1)^p$; the conjecture asserts that there are no others.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Catalan.lean); E. Katz and K. Pratt, On the Lebesgue-Nagell equation $x^2-2=y^p$, arXiv:2507.12397

import Mathlib

namespace FCP.Diophantine

theorem lebesgue_nagell (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ) :
    x ^ 2 - 2 = y ^ p ↔ (x = 1 ∨ x = -1) ∧ y = -1 := by sorry

end FCP.Diophantine
