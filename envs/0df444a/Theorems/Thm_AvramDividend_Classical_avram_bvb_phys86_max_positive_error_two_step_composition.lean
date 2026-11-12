-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys86_max_positive_error_two_step_composition
-- name    : AvramDividend.Classical.avram_bvb_phys86_max_positive_error_two_step_composition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:59:30.52123+00:00
-- url     : https://prove2.me/theorems/bc0b45a6-eccb-4acc-8d18-8b349cbf5c25
-- title:
--   Two-stage vanishing positive error composition for discounted cash bounds
-- statement:
--   If a discounted stopped cash sequence is asymptotically below an intermediate drift grid and that drift grid is asymptotically below the compensated generator grid, then the cash is asymptotically below the compensated generator grid. This elementary real-valued squeeze lemma is the Lean assembly step linking phys84 and phys85 to original physical deterministic cash phys82.
-- source:
--   Assembling original BV cash obligations phys84 and phys85

import Mathlib

open Filter
open scoped Topology
noncomputable section

/-- Two vanishing positive errors compose through an intermediate frozen
drift grid, yielding the generator-compensated cash inequality. -/

theorem AvramDividend.Classical.avram_bvb_phys86_max_positive_error_two_step_composition (F G K L : ℕ → ℝ) (w : ℝ)
    (hCash : Tendsto (fun n => max (F n - (w + L n)) 0)
      atTop (𝓝 (0 : ℝ)))
    (hComp : Tendsto (fun n => max (L n - (G n - K n)) 0)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => max (F n - (w + (-K n + G n))) 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
