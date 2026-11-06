-- Prove2me | solution 1 for isLittleO_const_of_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:58.849215+00:00
-- url     : https://prove2.me/submissions/0c10bfda-b27a-4fac-ab2d-04e1ab8936e4

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Filter Asymptotics

theorem solution {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  rw [isLittleO_const_left]
  exact Or.inr (tendsto_norm_atTop_atTop.comp hf)
