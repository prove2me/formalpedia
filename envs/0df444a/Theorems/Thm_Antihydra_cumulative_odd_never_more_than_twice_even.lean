-- Prove2me | Theorems.Thm_Antihydra_cumulative_odd_never_more_than_twice_even
-- name    : Antihydra.cumulative_odd_never_more_than_twice_even
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-21T12:40:04.378025+00:00
-- url     : https://prove2.me/theorems/60523366-45b6-4e17-a477-a1e7280c5ecb
-- title:
--   The Antihydra Problem: The cumulative number of odd values in this sequence is never more than twice the cumulative number of even values.
-- statement:
--   Let $H_n = \left\lfloor \frac {3n}2 \right\rfloor$ and $a_0 = 8, a_n = H(a_{n-1})$.
--   The cumulative number of odd values in this sequence is never more than twice the cumulative number of even values.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean

namespace Antihydra
theorem cumulative_odd_never_more_than_twice_even
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, b n ≥ 0 := by
  sorry
end Antihydra
