-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a124_original_negative_Borel_physical_void_probability_exact_poisson_exponential_20261114
-- name    : AvramDividend.Classical.avram_a124_original_negative_Borel_physical_void_probability_exact_poisson_exponential_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T19:32:12.780192+00:00
-- url     : https://prove2.me/theorems/786aeafb-e510-4408-a980-fa4d58906e98
-- title:
--   Original finite-activity negative Borel marked-jump void probability has exact Poisson exponential law
-- statement:
--   For an original spectrally negative Lévy process with finite total negative activity and any negative Borel mark set B, the probability of no actual physical B-marked jump on (0,T] is exp(-Tν(B)). Prove from the arbitrary-Borel multiplicative void semigroup, its natural-time power identity and the original small-time zero-to-one jump intensity slope, without assuming the full Poisson count law.
-- source:
--   Proved wave7_06_real_void_semigroup_exp_limit; new A122 arbitrary Borel void natural-time power and A123 original finite-activity arbitrary Borel small-time void slope. The two source ingredients imply the exact exponential formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a124_original_negative_Borel_physical_void_probability_exact_poisson_exponential_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    (P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) = 0}).toReal =
      Real.exp (-((T : ℝ) * (X.ν B).toReal)) := by sorry
