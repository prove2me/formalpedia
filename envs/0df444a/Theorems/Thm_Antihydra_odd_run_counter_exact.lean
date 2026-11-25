-- Prove2me | Theorems.Thm_Antihydra_odd_run_counter_exact
-- name    : Antihydra.odd_run_counter_exact
-- status  : Proved
-- author  : @sammas24
-- created : 2026-11-25T12:35:07.938379+00:00
-- url     : https://prove2.me/theorems/de43a532-5d0a-5362-b11b-9b75905a61b0
-- title:
--   Exact counter change across an Antihydra odd run
-- statement:
--   Let $a_n\ge2$ be any Antihydra trajectory and let an integer counter $b_n$ gain two on even states and lose one on odd states. Set $r_n=v_2(a_n-1)$, where $v_2$ is the exponent of two dividing a positive integer. Then
--
--   $$b_{n+r_n}=b_n-r_n.$$
--
--   This exact counter identity applies at any starting time, independently of the distinguished initial value eight or initial counter zero. It relates the reserve needed at a state to the counter at the end of its following odd run; at an even state $r_n=0$.
-- source:
--   Derived from BMO#2, beaver_math_olympiad_problem_2_antihydra, https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean. The counter identity and endpoint reduction are supporting derivations, not quotations. The finite horizon comes from the existing proved Antihydra.nonneg_first_100000 on Prove2Me.

import Definitions.Def_AntihydraTwoOrder

theorem Antihydra.odd_run_counter_exact
    (a : Nat → Nat) (b : Nat → Int)
    (ha : ∀ n, 2 ≤ a n)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, b (n + Antihydra.twoOrder (a n - 1)) =
      b n - (Antihydra.twoOrder (a n - 1) : Int) := by sorry
