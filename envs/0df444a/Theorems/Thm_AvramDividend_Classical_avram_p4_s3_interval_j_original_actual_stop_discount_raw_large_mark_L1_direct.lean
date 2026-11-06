-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_j_original_actual_stop_discount_raw_large_mark_L1_direct
-- name    : AvramDividend.Classical.avram_p4_s3_interval_j_original_actual_stop_discount_raw_large_mark_L1_direct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:13:00.676886+00:00
-- url     : https://prove2.me/theorems/3a60b114-1650-4c4b-bbd7-6295faad4651
-- title:
--   Same original X/D stopped discounted raw large-negative-mark generator integrable directly under cap
-- statement:
--   On the actual original X,D physical predictable filtration, the survival-killed discounted large-negative-jump generator 1_{t≤τ} exp(-q t)(w(Y_{t-}+z)-w(Y_{t-})) is L1 in finite predictable time-path μ times original Lévy ν restricted to z<-ε. Requires explicitly Y∈[0,v] on survival, q≥0, and continuous w supported nonnegative. No synthetic process or hidden clock-based state bound.
-- source:
--   Source-exact direct bridge to public stronger localised weighted large-mark L1 theorem 91881f55. The original physical pre-jump reserve is strongly predictable, actual survival set predictable, deterministic exp(-q t) strongly predictable and uniformly bounded by 1 for q≥0. Apply 91881 with R=Y, A=survival and a=discount, then identify its marked indicator with the literal original stopped discounted generator. No interim proxy process.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_raw_large_mark_L1
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_j_original_actual_stop_discount_raw_large_mark_L1_direct
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
    (q : ℝ) (hq : 0 ≤ q)
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
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Y p.1 + p.2) - w (Y p.1))
        else 0)
      (μ.prod (X.ν.restrict (Iio (-ε))))) := by sorry
