-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_single_positive_clock_reset_affine_jump_contact
-- name    : AvramDividend.Classical.avram_bv_tail12_single_positive_clock_reset_affine_jump_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:34:00.214899+00:00
-- url     : https://prove2.me/theorems/d6568984-e4b4-4b41-b2a3-4ba1dfee60ba
-- title:
--   Positive-clock single-reset strategy satisfies the original affine jump-contact inequality
-- statement:
--   For a genuine original spectrally negative Levy process, a single nonnegative dividend step paid strictly to the right of a positive deterministic clock satisfies the exact canonical affine candidate right-jump contact whenever the step pays the entire pre-dividend reserve at that clock before ruin. The zero clock and every other time have no right dividend jump.
-- source:
--   Original-process jump-contact interface for canonical 0b2da5b3, complementing Proved public 43840985 positive-clock admissibility and abf88d78 canonical HJB hypotheses.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail12_single_positive_clock_reset_affine_jump_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (s : ℝ≥0) (hs : 0 < s) (K : Ω → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω)
    (hright : ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω)
    (hK : ∀ ω, 0 ≤ K ω)
    (hreset : ∀ ω, (s : ℝ≥0∞) < ruinTime X x D ω →
      K ω = x + X.X s ω) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        (fun y : ℝ => if y < 0 then 0 else 1 + y) (riskProcess X x D t ω) -
          (fun y : ℝ => if y < 0 then 0 else 1 + y)
            (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by sorry
