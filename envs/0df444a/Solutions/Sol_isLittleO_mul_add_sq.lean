-- Prove2me | solution 1 for isLittleO_mul_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:10.391601+00:00
-- url     : https://prove2.me/submissions/05e9aaf1-9b39-454a-bc79-c89ec66cfb3b

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter Asymptotics
open scoped Topology

private theorem isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

theorem solution (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left
    simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)
