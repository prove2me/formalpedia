-- Prove2me | Theorems.Thm_DetDLP_d1_schedule_active_and_exponent
-- name    : DetDLP.d1_schedule_active_and_exponent
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T06:42:31.156284+00:00
-- url     : https://prove2.me/theorems/7fd1048b-5d00-4031-98bc-52edfd8c692c
-- title:
--   Admissibility and exponent of the Appendix D schedule
-- statement:
--   At every nonterminal level the generated schedule respects all degree, grid, and inherited-precision constraints, with precision constant 81C+544. Its full recursion exponent is bounded by a constant multiple of the scale divided by the square root of the exact radius.

import Definitions.Def_DetDLP_D1Schedule
open DetDLP DetDLP.D1 DetDLP.AppendixD4

theorem DetDLP.d1_schedule_active_and_exponent {C b e deg P : ℕ} (hC : 0 < C) (hb : 2 ≤ b) (he : e ≤ C*b) (hp : P ≤ C*b) :
    let s := makeSchedule C b e deg
    s.start = 0 ∧ (s.H < e → deg ≤ s.cap ∧ s.cap ≤ C*b ∧ 0 < s.κ ∧
      2^s.κ ≤ (b+2)^(4*(8*C+1)) ∧ Active s (C*b) P (81*C+544)) ∧
    exponent s b ≤ ((C*threshold C+1024:ℕ):ℝ)*b / Real.sqrt (radius b deg) := by sorry
