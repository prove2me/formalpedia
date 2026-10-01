-- Prove2me | Theorems.Thm_Brocard_berndt_galway_block_0
-- name    : Brocard.berndt_galway_block_0
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T01:36:57.353152+00:00
-- url     : https://prove2.me/theorems/b5287455-6987-47d5-b3a1-81e30e1a4dc5
-- title:
--   Brocard's equation $n!+1=m^2$ for $n < 10^8$: only $n=4,5,7$
-- statement:
--   Let $n$ and $m$ be natural numbers with $n < 10^8$. If
--   $$n! + 1 = m^2,$$
--   then $n \in \{4, 5, 7\}$.
--
--   This is the first of ten blocks of length $10^8$ into which the Berndt–Galway search range $n < 10^9$ for Brocard's equation is divided. It contains the three known solutions $4!+1 = 5^2$, $5!+1 = 11^2$, $7!+1 = 71^2$, and asserts that there are no others in this block.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard–Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), 41–42 (computer search for n < 10^9); one of ten blocks of the milestone Brocard.berndt_galway_search.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_block_0 (n m : ℕ) (hn : n < 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by sorry

end Brocard
