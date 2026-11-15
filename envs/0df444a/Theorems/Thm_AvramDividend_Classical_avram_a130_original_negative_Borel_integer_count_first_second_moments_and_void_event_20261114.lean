-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a130_original_negative_Borel_integer_count_first_second_moments_and_void_event_20261114
-- name    : AvramDividend.Classical.avram_a130_original_negative_Borel_integer_count_first_second_moments_and_void_event_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T19:43:33.444715+00:00
-- url     : https://prove2.me/theorems/83c09b5d-b122-490b-bd7c-f1c2f1bdaa62
-- title:
--   Original finite-negative-activity Borel physical jump count has an integer representative with exact first and second moments and the same zero event
-- statement:
--   At finite negative Lévy activity, construct a measurable natural count K on the original process probability space with the exact physical Borel jump count's first moment r=Tν(B), second moment r²+r, first and squared integrability, and identical probability of zero actual physical B-jumps. This packages already Proved count realisation and moment identities, plus the explicit source-finite-a.e. event-transfer theorem A128. It does not assume the Poisson law.
-- source:
--   Proved A20 natural count representation; JA35 exact first moment and integrability; A20 exact second moment; A128 physical zero-event probability correspondence. Original probability measure P throughout.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a130_original_negative_Borel_integer_count_first_second_moments_and_void_event_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let r : ℝ := (T : ℝ) * (X.ν B).toReal
    ∃ K : Ω → ℕ,
      Measurable K ∧
      Integrable (fun ω => (K ω : ℝ)) P ∧
      Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ∂P) = r ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) = r ^ 2 + r ∧
      P {ω : Ω | K ω = 0} =
        P {ω : Ω |
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) = 0} := by sorry
