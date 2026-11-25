-- Prove2me | Theorems.Thm_Erdos406_known_examples
-- name    : Erdos406.known_examples
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-25T11:31:24.757814+00:00
-- url     : https://prove2.me/theorems/c3a0610e-bb7d-4a11-b41e-9bcd63412af2
-- title:
--   Erdős 406: the three known examples $1, 4, 256$
-- statement:
--   Among powers of two, the only known natural numbers whose base-3 expansion uses only the digits $0$ and $1$ are $1 = 2^0$, $4 = 1 + 3 = 2^2$ and $256 = 1 + 3 + 3^2 + 3^5 = 2^8$.
--
--   $$1 = 1_3,\qquad 4 = 11_3,\qquad 256 = 100111_3 .$$
--
--   This milestone records that these three concrete powers satisfy the digit condition.
--
--   **Formalization Note** `Nat.digits 3 m` is the list of base-3 digits of $m$ in least-significant-first order; list containment in $[0,1]$ says every digit is $0$ or $1$.
-- source:
--   https://www.erdosproblems.com/406 — the three examples listed in the problem statement

import Mathlib

namespace Erdos406

theorem known_examples :
    Nat.digits 3 (2 ^ 0) ⊆ [0, 1] ∧
    Nat.digits 3 (2 ^ 2) ⊆ [0, 1] ∧
    Nat.digits 3 (2 ^ 8) ⊆ [0, 1] := by
  sorry

end Erdos406
