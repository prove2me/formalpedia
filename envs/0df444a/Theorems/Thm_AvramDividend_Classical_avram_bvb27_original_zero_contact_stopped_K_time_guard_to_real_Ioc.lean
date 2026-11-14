-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_zero_contact_stopped_K_time_guard_to_real_Ioc
-- name    : AvramDividend.Classical.avram_bvb27_original_zero_contact_stopped_K_time_guard_to_real_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:04:39.750025+00:00
-- url     : https://prove2.me/theorems/43b8894a-08dc-4314-b0cf-f32adbe5a54d
-- title:
--   Original BV zero-survival stopped K physical NNReal mapped-time integral converted to real discounted clipped-prefix Ioc integral
-- statement:
--   Preserve the actual original source controlled reserve, finite observation horizon, exact stopping guard, physical clipping, full negative Lévy measure and discount. Show physical NNReal mapped-time integral converted to real discounted clipped-prefix Ioc integral. Together these two mathematically independent steps prove the exact original stopped negative-mark compensator K_n formula of parent 57da0020, which is needed for source zero-reserve survival ed067740. No surrogate clock or mark intensity.
-- source:
--   Original source ed067740 K, accepted full global mark guard ede92794, original restricted mark integration aa8daed6, mapped time measure 18508f5d, clipped real discount fb4a3f35.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb27_original_zero_contact_stopped_K_time_guard_to_real_Ioc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (q T : ℝ) (hT : 0 < T) (ω : Ω)
    (S : ℝ≥0) (hS : (S : ℝ) = T)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
       X.X t ω = (t : ℝ) * X.drift)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
       riskProcess X x D t ω = 0)
    (hSurvival : (S : ℝ≥0∞) < ruinTime X x D ω) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → ℝ≥0 → ℝ → ℝ := fun n t z =>
      if 0 < t ∧ (t : ℝ) < T - δ n ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t)) else 0
    let K : ℕ → ℝ := fun n =>
      ∫ t, ∫ z, H n t z ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ n : ℕ,
      (∫ t : ℝ≥0,
        (if 0 < t ∧ (t : ℝ) < T - δ n ∧
             (t : ℝ≥0∞) ≤ ruinTime X x D ω then
           -(Real.exp (-(q * (t : ℝ))) * w 0) *
             (X.ν (Iio (0 : ℝ))).toReal
         else 0)
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
        -(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ t in Ioc (0 : ℝ) (T - δ n),
            Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by sorry
