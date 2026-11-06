-- Prove2me | solution 1 for summable_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:24:27.318+00:00
-- url     : https://prove2.me/submissions/88eb3f66-a7fb-497b-be8d-4de05ee5c972

import Mathlib.Analysis.Normed.Group.Tannery

open Filter

theorem solution {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  exact summable_congr_atTop huv
