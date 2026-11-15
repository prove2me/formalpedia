-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_count_condexp_from_negative_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_count_condexp_from_negative_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:57:32.059004+00:00
-- url     : https://prove2.me/theorems/316e04ce-4f29-4fb8-9945-c2f88420834c
-- title:
--   Deterministic conditional expectation of original marked count from negative Lévy rate
-- statement:
--   For finite ν-mass marks, the conditional expectation of the actual original intrinsic count on (s,t]×B given the real past filtration equals (t-s)ν(B), assuming only the unconditional source identity for marks in B∩(-∞,0).
-- source:
--   Proved original conditional expected marked count b87b82e9 and full Borel rate-of-negative original bridge 9de6cb12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_count_condexp_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_borel_rate_of_negative_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Given the original process's unconditional marked Levy rate, the
conditional expected marked count at its actual past filtration is that
deterministic rate. This uses original future/past independence. -/

theorem AvramDividend.Classical.avram_p2_e_compensator_original_count_condexp_from_negative_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hNegativeRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)) =ᵐ[P]
      (fun _ : Ω => (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) := by sorry
