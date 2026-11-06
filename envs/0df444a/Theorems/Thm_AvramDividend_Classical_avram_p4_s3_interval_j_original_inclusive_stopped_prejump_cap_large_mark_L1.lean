-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_j_original_inclusive_stopped_prejump_cap_large_mark_L1
-- name    : AvramDividend.Classical.avram_p4_s3_interval_j_original_inclusive_stopped_prejump_cap_large_mark_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:03:22.169201+00:00
-- url     : https://prove2.me/theorems/4b0c5441-b5bc-49b4-a2ab-09b00737e3a1
-- title:
--   Actual original stopped pre-jump reserve cap gives finite large-negative-Lévy-mark L1 kernel
-- statement:
--   For the original physical SpectrallyNegativeLevy X and dividend strategy D, the true inclusive stopped pre-jump reserve is predictable. Under an explicit pointwise bound 0≤Y_{t-}≤v on survival, the stopped-clipped reserve R has Borel integrable raw large negative jump values w(R+z)-w(R) on any finite predictable time-path measure times ν restricted to z<-ε. No boundedness is inferred from τ alone.
-- source:
--   Use original true pre-jump reserve strongly predictable, actual stopping survival strongly predictable, multiply to obtain measurable R, verify R lies in [0,v] under explicit on-survival cap. Then apply the accepted original large-jump L1 theorem b40bbce6. Source-faithful physically bound stopped reserve, true ν and real marks. Statement fix: bind the predictable measurable-space instance locally in the target proposition to make μ.prod elaborate in that sigma algebra.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_j_original_inclusive_stopped_prejump_cap_large_mark_L1
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
     let R : ℝ≥0 × Ω → ℝ := fun p =>
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0) * Y p;
     Integrable
      (fun p : (ℝ≥0 × Ω) × ℝ => w (R p.1 + p.2) - w (R p.1))
      (μ.prod (X.ν.restrict (Iio (-ε))))) := by sorry
