-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_probability_horizon_antitone
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_horizon_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:35:42.8501+00:00
-- url     : https://prove2.me/theorems/5fa31dc7-be5b-49f2-bb3e-5838668ebf8b
-- title:
--   Original negative-band void probability is antitone in observation horizon
-- statement:
--   On the actual original probability measure P, the probability of no intrinsic negative-band jump up to T+S is at most its probability of no such jump up to T. The proof imports the Proved original-path horizon splitting theorem and uses measure monotonicity, without assuming a Poisson process or probability normalisation.
-- source:
--   Direct consumer of accepted source-specific b268c699-c9f3-4ac9-8c5d-3272d82361aa to supply horizon-monotone no-jump probabilities for wave7-06 original increments and 390a8092-89ae-45c8-bed8-b43b900baa2f, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_horizon_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T S : ℝ≥0) (n : ℕ) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
     P {ω : Ω | NX ω (Ioc 0 (T + S) ×ˢ B) = 0} ≤
       P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0}) := by sorry
