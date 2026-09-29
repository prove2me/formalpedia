-- Prove2me | Theorems.Thm_Devaney_exists_fixedPoint_of_covers_self
-- name    : Devaney.exists_fixedPoint_of_covers_self
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T07:15:00.806963+00:00
-- url     : https://prove2.me/theorems/f16d9cb1-bde8-4cf4-b7d7-8f54296119bd
-- title:
--   First covering observation — an interval covering itself contains a fixed point
-- statement:
--   Let $f$ be continuous and let $[a,b]$ be a closed interval whose image covers it, $[a,b] \subseteq f([a,b])$. Then $f$ has a fixed point in $[a,b]$.
--
--   This is the intermediate value theorem in dynamical clothing, and it is the first of the two observations on which Devaney's proof of Sarkovskii's theorem rests.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, p. 60, first observation in the proof of Theorem 10.1

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem exists_fixedPoint_of_covers_self (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ)
    (hab : a ≤ b) (h : Covers f (Set.Icc a b) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = x := by sorry
end Devaney
