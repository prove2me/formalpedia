-- Prove2me | Theorems.Thm_FCP_Diophantine_pillai_conjecture
-- name    : FCP.Diophantine.pillai_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:27:23.414068+00:00
-- url     : https://prove2.me/theorems/327271e8-2034-447a-ac9a-ac595d24aaa1
-- title:
--   Pillai's conjecture: $ax^n - by^m = c$ has finitely many solutions
-- statement:
--   **Pillai's conjecture.** For fixed positive integers $a, b, c$, the equation
--   $$a x^{n} - b y^{m} = c$$
--   has only finitely many solutions in integers $x, y, m, n > 1$ with $(m, n) \ne (2, 2)$. Equivalently, consecutive perfect powers become arbitrarily far apart. The special case $a = b = c = 1$ was Catalan's conjecture, proved by Mihăilescu in 2004; the general statement remains open, and the exclusion of $(m,n) = (2,2)$ is necessary because Pell equations can have infinitely many solutions.
--
--   *Formalization note:* unlike the source statement, the equation is taken over $\mathbb{Z}$, so that no truncated natural subtraction is involved.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Catalan.lean); https://en.wikipedia.org/wiki/Catalan%27s_conjecture#Pillai's_conjecture

import Mathlib

namespace FCP.Diophantine

theorem pillai_conjecture (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    {q : ℕ × ℕ × ℕ × ℕ | 1 < q.1 ∧ 1 < q.2.1 ∧ 1 < q.2.2.1 ∧ 1 < q.2.2.2 ∧
      (q.2.2.1, q.2.2.2) ≠ (2, 2) ∧
      (a : ℤ) * q.1 ^ q.2.2.2 - b * q.2.1 ^ q.2.2.1 = c}.Finite := by sorry

end FCP.Diophantine
