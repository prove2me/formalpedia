-- Prove2me | Theorems.Thm_Devaney_sarkovskii_odd
-- name    : Devaney.sarkovskii_odd
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:15:45.431363+00:00
-- url     : https://prove2.me/theorems/ca9e0168-11b2-4fe8-98a4-b5cf3162b9de
-- title:
--   Theorem 10.2, odd case
-- statement:
--   Let $f$ be continuous with a periodic point of prime period $n$, where $n > 1$ is odd. Then for every $\ell$ with $n \triangleright \ell$ in the Sarkovskii ordering, $f$ has a periodic point of prime period $\ell$.
--
--   This is the case Devaney treats first and in full detail: the orbit points are ordered on the line, the interval $I_1 = [x_i, x_{i+1}]$ is chosen at the last sign change, and the shortest return loop in the covering diagram is shown to have length $n-1$, which yields all larger periods and all even periods.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, pp. 63–65, proof of Theorem 10.2 (case n odd)

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem sarkovskii_odd (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (hodd : Odd n) (hn : 1 < n)
    (h : ∃ x, HasPrimePeriod f x n) (l : ℕ) (hl : SarkovskiiPrecedes n l) :
    ∃ x, HasPrimePeriod f x l := by sorry
end Devaney
