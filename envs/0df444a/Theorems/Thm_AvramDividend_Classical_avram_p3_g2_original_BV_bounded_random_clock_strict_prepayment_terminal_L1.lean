-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
-- name    : AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:21:23.831234+00:00
-- url     : https://prove2.me/theorems/22a17c73-919a-44c9-aec3-3ea698298e00
-- title:
--   Original bounded BV random-clock prepayment terminal is integrable from actual physical source with no measurability or stopping-time assumptions
-- statement:
--   For the original bounded-variation Lévy process and actual adapted left-continuous dividend strategy, every bounded measurable random observation clock has an integrable discounted strict-survival prepayment HJB terminal under nonnegative initial capital and nonnegative discount. Joint original riskProcess measurability supplies the random evaluation, source ruinTime measurability supplies the strict survival event, and the independent uniform BV drift strip plus compact continuity supplies an L1 envelope. The physical t=0 atom and ruin-at-τ exclusion are preserved.
-- source:
--   New G2 original joint prepayment riskProcess measurable; Proved G2 f0d305a1 source measurable survival; resubmitted conditional prepayment L1 from 635fc873 original BV drift strip; no P3 canonical residual or E2/F2 Open theorem imported.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_measurable_random_clock_strict_ruin_survival_event
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1_of_source_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hFinite : IsFiniteMeasure P)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hwCont : ContinuousOn w (Ici 0))
    (hwMeas : Measurable w)
    (q : ℝ) (hq : 0 ≤ q)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω => if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (τ ω : ℝ))) *
        w (riskProcess X x D (τ ω) ω)
    else 0) P := by sorry
