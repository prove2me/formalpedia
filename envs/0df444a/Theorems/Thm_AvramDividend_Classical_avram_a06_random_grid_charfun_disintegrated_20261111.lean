-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_grid_charfun_disintegrated_20261111
-- name    : AvramDividend.Classical.avram_a06_random_grid_charfun_disintegrated_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:28:40.966193+00:00
-- url     : https://prove2.me/theorems/97ceb190-769e-4854-acd8-930c744cd997
-- title:
--   Characteristic function of independent random count-grid marked vector disintegrates over deterministic grids
-- statement:
--   The exact Fubini/disintegration step for independent random count-grid and mark streams. Conditional on the count grid, the law of the marked increments is the fixed-grid law under the original mark distribution. This theorem requires only independence and measurability, not IID marks or the separate fixed-grid characteristic-power identity. Establish via the Proved random marked-vector product pushforward law and characteristic-function integral over the product measure.

import Mathlib
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_grid_charfun_disintegrated_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (t : WithLp 2 (Fin n → ℝ)) :
    MeasureTheory.charFun
      (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
    ∫ ω, MeasureTheory.charFun
      (Measure.map (fun ω' : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω')) P) t ∂P := by sorry
