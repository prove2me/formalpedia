-- Prove2me | Theorems.Thm_Antihydra_odd_step_twoOrder
-- name    : Antihydra.odd_step_twoOrder
-- status  : Proved
-- author  : @sammas24
-- created : 2026-11-24T18:57:16.784806+00:00
-- url     : https://prove2.me/theorems/01fc2d02-fcdc-4b0f-87b5-1729ba2f87d0
-- title:
--   An odd Antihydra step decreases the dyadic odd-run reserve by one
-- statement:
--   Let $x>1$ be odd, and put $H(x)=\lfloor3x/2\rfloor$. Writing $v_2(m)$ for the exponent of $2$ dividing the positive integer $m$, we have
--
--   $$
--   v_2(H(x)-1)+1=v_2(x-1).
--   $$
--
--   This identity describes one odd step of Antihydra: the number of odd steps remaining decreases by exactly one. It applies to every odd input greater than one, independently of the distinguished orbit starting at eight.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean (BMO#2, beaver_math_olympiad_problem_2_antihydra, recurrence a(n+1)=floor(3a(n)/2) and counter recurrence). Original supporting derivation from these recurrences; the valuation lemmas are not stated verbatim in the source.

import Definitions.Def_AntihydraTwoOrder

theorem Antihydra.odd_step_twoOrder (x : Nat) (hx : 1 < x) (hodd : x % 2 ≠ 0) :
    Antihydra.twoOrder ((3 * x) / 2 - 1) + 1 =
      Antihydra.twoOrder (x - 1) := by sorry
