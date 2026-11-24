-- Prove2me | Theorems.Thm_Antihydra_even_transition_budget
-- name    : Antihydra.even_transition_budget
-- status  : Open
-- author  : @sammas24
-- created : 2026-11-24T18:57:18.811895+00:00
-- url     : https://prove2.me/theorems/3ca785fa-b7d3-4ab6-8031-b918e35a30fb
-- title:
--   Antihydra: even steps leave enough counter for the following odd run
-- statement:
--   Let $a_n$ and $b_n$ be the original Antihydra sequences:
--
--   $$
--   a_0=8,\quad a_{n+1}=\lfloor3a_n/2\rfloor,\quad b_0=0,\quad b_{n+1}=\begin{cases}b_n+2,&a_n\text{ even},\\b_n-1,&a_n\text{ odd}.\end{cases}
--   $$
--
--   For every even state on this orbit, the following proposed budget estimate holds:
--
--   $$
--   a_n\equiv0\pmod2\quad\Longrightarrow\quad v_2\!\left(\lfloor3a_n/2\rfloor-1\right)\le b_n+2.
--   $$
--
--   Here $v_2(m)$ is the exponent of $2$ dividing a positive integer $m$. The estimate bounds the length of the odd run that can follow an even step by the counter available after that step. It is an open child conjecture in a reduction of the full Antihydra problem, not an established bound. Together with the general odd-step valuation identity, it yields the original nonnegative-counter conjecture by induction.
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/BeaverMathOlympiad.lean (BMO#2, beaver_math_olympiad_problem_2_antihydra, recurrence a(n+1)=floor(3a(n)/2) and counter recurrence). Original supporting derivation from these recurrences; the valuation lemmas are not stated verbatim in the source.

import Definitions.Def_AntihydraTwoOrder

theorem Antihydra.even_transition_budget
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, a n % 2 = 0 →
      (Antihydra.twoOrder ((3 * a n) / 2 - 1) : Int) ≤ b n + 2 := by sorry
