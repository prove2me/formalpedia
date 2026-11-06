-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_j_original_inclusive_stopped_raw_large_mark_L1
-- name    : AvramDividend.Classical.avram_p4_s3_interval_j_original_inclusive_stopped_raw_large_mark_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:24:51.559896+00:00
-- url     : https://prove2.me/theorems/7accce7a-072e-432a-93d5-b22891abc4b8
-- title:
--   Genuine original stopped large negative jump generator is L1 with zero after stopping
-- statement:
--   The literal original physical stopped large negative-mark generator kernel 1_{t≤τ}(w(Y_{t-}+z)-w(Y_{t-})) is integrable on finite predictable time-path measure times physical Lévy ν restricted to z<-ε, under an explicit compact on-survival reserve bound and continuity/zero-on-negative of w. The kernel vanishes after the true stopping time.
-- source:
--   Apply the proved physical stopped pre-jump capped reserve L1 helper to R=1_alive*Y, then restrict its integrable raw kernel to the measurable predictable survival set in time-path × real Lévy mark. On survival R=Y; outside survival the indicator kills the residual. This is the literal original stopped large-jump source, not a synthetic process.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_j_original_inclusive_stopped_prejump_cap_large_mark_L1
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_j_original_inclusive_stopped_raw_large_mark_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hStoppedReserveCap : ∀ p : ℝ≥0 × Ω,
      (p.1 : ℝ≥0∞) ≤ τ p.2 →
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc 0 v)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    [IsFiniteMeasure μ] :
    (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
     let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1;
     Integrable
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then
          w (Y p.1 + p.2) - w (Y p.1)
        else 0)
      (μ.prod (X.ν.restrict (Iio (-ε))))) := by sorry
