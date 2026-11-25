-- Prove2me | Theorems.Thm_Antihydra_tail_odd_run_endpoint_nonnegative
-- name    : Antihydra.tail_odd_run_endpoint_nonnegative
-- status  : Open
-- author  : @sammas24
-- created : 2026-11-25T12:35:10.082606+00:00
-- url     : https://prove2.me/theorems/f3ce5f67-1b24-59e1-bb94-f537dd920344
-- title:
--   Antihydra: nonnegative odd-run endpoints beyond the verified prefix
-- statement:
--   Let $a_0=8$, $b_0=0$ and use the original Antihydra recurrence and counter update. For a state at time $n$, put
--
--   $$r_n=v_2(\lfloor3a_n/2\rfloor-1),\qquad m_n=n+1+r_n.$$
--
--   The proposed tail checkpoint estimate is
--
--   $$a_n\equiv2\pmod4,\quad b_n\ge0,\quad m_n>100000\quad\Longrightarrow\quad b_{m_n}\ge0.$$
--
--   Here $m_n$ is the endpoint of the odd run following the even state at time $n$. This is an open child conjecture, not a proved tail bound. It isolates sparse run endpoints beyond the already verified finite horizon. The exact odd-run counter identity and the proved first-100000 bound connect this obligation to the entry-budget frontier.
-- source:
--   Derived from BMO#2, beaver_math_olympiad_problem_2_antihydra, https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean. The counter identity and endpoint reduction are supporting derivations, not quotations. The finite horizon comes from the existing proved Antihydra.nonneg_first_100000 on Prove2Me.

import Definitions.Def_AntihydraTwoOrder

theorem Antihydra.tail_odd_run_endpoint_nonnegative
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, a n % 4 = 2 → 0 ≤ b n →
      100000 < n + 1 + Antihydra.twoOrder ((3 * a n) / 2 - 1) →
      0 ≤ b (n + 1 + Antihydra.twoOrder ((3 * a n) / 2 - 1)) := by sorry
