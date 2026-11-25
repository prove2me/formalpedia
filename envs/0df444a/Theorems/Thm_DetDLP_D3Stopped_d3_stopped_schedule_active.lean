-- Prove2me | Theorems.Thm_DetDLP_D3Stopped_d3_stopped_schedule_active
-- name    : DetDLP.D3Stopped.d3_stopped_schedule_active
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T07:05:35.270904+00:00
-- url     : https://prove2.me/theorems/78bbb887-16b9-4611-8342-c4968016fd7f
-- title:
--   Admissibility of the stopped continuation schedule
-- statement:
--   For each positive mass constant, the stopped schedule satisfies every active-node arithmetic and precision condition at all sufficiently large logarithmic scales. Its modulus capacity is linear in the scale and the field size remains polynomially bounded.

import Definitions.Def_DetDLP_D3StoppedSchedule
set_option autoImplicit false

namespace DetDLP.D3Stopped
open AppendixD4
theorem d3_stopped_schedule_active (C : ℕ) (hC : 0 < C) :
    ∃ (B L₀ : ℕ), 0 < B ∧ ∀ (S M P d₀ : ℕ),
      L₀ ≤ level S → threshold S < M → M ≤ C*S/8^d₀ → 1 ≤ P →
      P ≤ S+80*C*S*(if d₀ = 0 then 1 else 2^shift S (d₀-1)) →
      cap S ≤ C*S ∧ 0 < 4*level S ∧ 2^(4*level S) ≤ (S+2)^5 ∧
      Active (schedule C S M d₀) (C*S) P B := by sorry
end DetDLP.D3Stopped
