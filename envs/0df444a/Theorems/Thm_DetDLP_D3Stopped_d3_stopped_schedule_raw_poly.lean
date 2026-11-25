-- Prove2me | Theorems.Thm_DetDLP_D3Stopped_d3_stopped_schedule_raw_poly
-- name    : DetDLP.D3Stopped.d3_stopped_schedule_raw_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T06:47:20.550529+00:00
-- url     : https://prove2.me/theorems/11094c71-78d0-428b-8fdf-2affdaa52c87
-- title:
--   Polynomial-time generation of the stopped schedule
-- statement:
--   For any fixed coefficient $C$, the stopped schedule can be generated in polynomial time on raw bitstrings. On a valid contraction instance, the output is exactly the canonical schedule encoding for its scale, edge count, starting depth and polynomial coefficient word.

import Definitions.Def_DetDLP_D3StoppedRaw
set_option autoImplicit false

namespace DetDLP.D3Stopped
open AppendixD4 Polynomial
theorem d3_stopped_schedule_raw_poly (C : ℕ) : Groundwork.PolyT (scheduleRaw C) ∧ ∀ (d₀ S P l : ℕ) (payload : Bits) (G : Graph) (f : ℤ[X]),
    scheduleRaw C (encodeBTNInstance (descOf d₀ f payload) G S P l) = (schedule C S G.nE d₀).bits f := by sorry
end DetDLP.D3Stopped
