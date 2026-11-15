-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
-- name    : AvramDividend.Classical.avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T19:31:59.316208+00:00
-- url     : https://prove2.me/theorems/525f1cfe-e83d-4dd1-9eb6-26b59ff6c568
-- title:
--   Original negative Borel physical-jump void probability has exact small-time intensity slope for finite activity
-- statement:
--   For finite negative activity and any negative Borel mark set B, the probability of at least one actual physical B-marked jump during the short horizon T/n has asymptotic n-scaled limit T ν(B), on the original Lévy probability space. This is the infinitesimal arrival-rate component of the arbitrary Borel Poisson count law, and can be established using the exact first and second physical count moments and positive count finiteness without assuming an existing Poisson law.
-- source:
--   Proved JA35 physical Borel count first moment and A20 second factorial moment; the simple inequalities E N - E N(N-1) <= P(N>0) <= E N imply the short-time slope since EN=λ/n and E N(N-1)=O(1/n²).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a123_original_arbitrary_negative_Borel_void_smalltime_rate_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) * (1 -
          (P {ω : Ω |
            ((Measure.count.restrict {u : ℝ≥0 |
              0 < u ∧ X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal))
      Filter.atTop (nhds ((T : ℝ) * (X.ν B).toReal)) := by sorry
