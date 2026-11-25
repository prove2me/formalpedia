-- Prove2me | Theorems.Thm_Antihydra_odd_run_entry_budget
-- name    : Antihydra.odd_run_entry_budget
-- status  : Open
-- author  : @sammas24
-- created : 2026-11-25T11:33:41.389217+00:00
-- url     : https://prove2.me/theorems/ae9b9bb1-0ffc-5b4f-bafa-faec867fabc5
-- title:
--   Antihydra: conditional counter reserve at even-to-odd transitions
-- statement:
--   Let the original Antihydra orbit satisfy
--
--   $$
--   a_0=8,\quad a_{n+1}=H(a_n),\quad H(x)=\lfloor3x/2\rfloor,\quad b_0=0,
--   $$
--
--   with the counter increasing by two on even states and decreasing by one on odd states. Write $v_2(m)$ for the exponent of two dividing a positive integer $m$.
--
--   The proposed conditional estimate is
--
--   $$
--   a_n\equiv2\pmod4,\quad b_n\ge0\quad\Longrightarrow\quad v_2(H(a_n)-1)\le b_n+2.
--   $$
--
--   These are exactly the even states whose next state is odd. The condition asks that, whenever the current counter is nonnegative, the even step supplies enough reserve for the ensuing odd run. It is an open child conjecture, not an established inequality. It isolates the remaining invariant-preservation obligation after the automatic odd and even-to-even transitions have been discharged.
-- source:
--   Derived modulo-four refinement of BMO#2, beaver_math_olympiad_problem_2_antihydra, https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean. Uses the displayed original recurrence and initial conditions; this supporting refinement is not stated verbatim in that source.

import Definitions.Def_AntihydraTwoOrder

theorem Antihydra.odd_run_entry_budget
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, a n % 4 = 2 → 0 ≤ b n →
      (Antihydra.twoOrder ((3 * a n) / 2 - 1) : Int) ≤ b n + 2 := by sorry
