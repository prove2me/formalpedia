-- Prove2me | Theorems.Thm_FCP_Diophantine_catalan_conjecture
-- name    : FCP.Diophantine.catalan_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:43:01.020822+00:00
-- url     : https://prove2.me/theorems/e4ef6874-6fa5-4362-9b9d-36e9dd4ddcab
-- title:
--   Catalan's conjecture (Mihăilescu's theorem): $3^2 - 2^3 = 1$ is the only solution
-- statement:
--   **Mihăilescu's theorem (Catalan's conjecture, 2002).** The only solution in integers $x, y > 0$ and exponents $a, b > 1$ of
--   $$x^{a} - y^{b} = 1$$
--   is $3^2 - 2^3 = 1$. In other words, $8$ and $9$ are the only consecutive perfect powers. The theorem is proved but, to our knowledge, not yet formalized in Lean; it is included as the solved anchor of the Diophantine group of this mission.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Catalan.lean); P. Mihăilescu, Primary cyclotomic units and a proof of Catalan's conjecture, J. reine angew. Math. 572 (2004), 167--195

import Mathlib

namespace FCP.Diophantine

theorem catalan_conjecture (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y)
    (heq : (x : ℤ) ^ a - (y : ℤ) ^ b = 1) : a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := by sorry

end FCP.Diophantine
