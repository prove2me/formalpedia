-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_local_reserve_of_continuity_nonnegative_mark
-- name    : AvramDividend.Classical.avram_e0_initial_step_local_reserve_of_continuity_nonnegative_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:39:55.644097+00:00
-- url     : https://prove2.me/theorems/de475cd8-288e-43d0-a747-927e1e5a5719
-- title:
--   A nonnegative affordable initial mark leaves nonnegative original reserve locally
-- statement:
--   A nonnegative initial dividend mark strictly below x implies x>0. A source path continuous at zero with X(0)=0 remains above the negative residual margin for all sufficiently small positive times, while the zero-clock risk reserve equals x. Consequently riskProcess is nonnegative throughout some full initial interval, supplying the proved positive-ruin-time lemma.
-- source:
--   Corrects missing x≥0 hypothesis in earlier Open source target f6cbd410; original riskProcess subtracts D(t), not rightLimit D(t). Explicitly splits time zero and t>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_step_local_reserve_of_continuity_nonnegative_mark
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ) (ω : Ω)
    (hKnonneg : 0 ≤ K ω)
    (hzero : X.X 0 ω = 0)
    (hcont : ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0)
    (hgap : K ω < x) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ →
      0 ≤ riskProcess X x (fun s η => if s = 0 then 0 else K η) t ω := by sorry
