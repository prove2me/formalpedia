-- Prove2me | Theorems.Thm_Erdos287_cleared_denominator_cap_iff
-- name    : Erdos287.cleared_denominator_cap_iff
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:37:28.241859+00:00
-- url     : https://prove2.me/theorems/2487e264-c712-574d-be49-8542c680131d
-- title:
--   Denominator caps as divisibility of the cleared numerator
-- statement:
--   For $L>0$ and natural numbers $W,C$, the reduced denominator of $W/L$ divides $C$ if and only if $L/\gcd(L,C)$ divides $W$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.cleared_denominator_cap_iff (W L C : ℕ) (hL : 0 < L) :
    ((W : ℚ) / L).den ∣ C ↔ L / L.gcd C ∣ W := by sorry
