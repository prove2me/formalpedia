-- Prove2me | Theorems.Thm_CannonFloydParry_exists_biInvariant_linearOrder
-- name    : CannonFloydParry.exists_biInvariant_linearOrder
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:31:34.413166+00:00
-- url     : https://prove2.me/theorems/7d367536-2f07-41b8-ac6f-88e2d3dbc5fb
-- title:
--   $F$ is a totally ordered group
-- statement:
--   Thompson's group $F$ is a totally ordered group: there is a linear order on $F$ such
--   that whenever $a \le b$, both $ca \le cb$ and $ac \le bc$ hold for every $c$ in $F$.
--
--   Cannon-Floyd-Parry construct such an order from the set $P$ of order positive elements, those
--   $f \in F$ for which there is a subinterval $[a,b]$ of $[0,1]$ on which the derivative of $f$ is
--   less than $1$ and with $f(x) = x$ for $0 \le x \le a$; they check that $F$ is the disjoint union
--   of $P^{-1}$, $\{1\}$ and $P$, that $P$ is closed under multiplication, and that $P$ is closed
--   under conjugation. They note the result also follows from Brin and Squier.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Theorem 4.11, p. 233

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem exists_biInvariant_linearOrder :
    ∃ l : LinearOrder F, ∀ a b c : F, l.le a b → l.le (c * a) (c * b) ∧ l.le (a * c) (b * c) := by
  sorry

end CannonFloydParry
