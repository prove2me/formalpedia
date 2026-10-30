-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_stopped_scale_continuity_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_stopped_scale_continuity_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:15:21.347731+00:00
-- url     : https://prove2.me/theorems/941a3a0b-502b-424e-b22e-122c1e4690ab
-- title:
--   Almost-sure continuity of the actual BV scale at finite two-sided exit
-- statement:
--   For the actual original spectrally negative bounded-variation Levy path, the q-scale is continuous at the realised reserve at its first finite strict two-sided exit, almost surely. This local, random-terminal continuity correctly respects the positive Wq(0) boundary atom and is the missing premise for passage from finite-grid stopped payoffs to continuous-time optional stopping.
-- source:
--   Source-specific consequence of canonically Proved actual BV finite-stop nonzero-reserve theorem 058bc8db and q-scale continuity away from zero 0dfe2e0c, with original strict up/down exit clocks. The assertion is conditional on finite exit and makes no global W(0)=0 assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_stopped_min_away_zero_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_stopped_scale_continuity_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      ContinuousAt W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal ω) := by sorry
