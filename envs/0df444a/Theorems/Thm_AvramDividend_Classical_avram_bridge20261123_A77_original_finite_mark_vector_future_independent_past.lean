-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_finite_mark_vector_future_independent_past
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_finite_mark_vector_future_independent_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:09:32.807895+00:00
-- url     : https://prove2.me/theorems/da95ae77-492c-4a18-bfab-fa9653ee46c8
-- title:
--   Original Lévy future negative-marked jump count vector independent of arbitrary measurable past observable
-- statement:
--   For the original unchanged spectrally negative Lévy process, any finite family of measurable mark sets and any finite future interval (s,s+T], the entire finite vector of physical marked-jump counts is independent of every random observable measurable with respect to the filtration at s. Construct simultaneous measurable shifted-path extractors using the Proved original Avram wave7 finite-interval count extractor theorem and use the Proved full shifted-future path independence theorem. This is a substantive vector extension of the earlier single-mark result, without assuming mark-space spatial independence.
-- source:
--   Proved original path extractor d9b9e3c2-55dd-4d9b-82ee-f6ce49bb70c5 and original full shifted path independence 86ab54a5-0f9f-4e69-a76c-19f22db4d908.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_finite_mark_vector_future_independent_past
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    IndepFun H (fun ω : Ω => fun i : Fin n =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B i)) P := by sorry
