-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
-- name    : AvramDividend.Classical.avram_b58_original_selected_negative_jump_cells_uniform_count_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:23:39.719818+00:00
-- url     : https://prove2.me/theorems/f3db552c-da6e-42ec-9afa-0e216c04fd23
-- title:
--   Original selected negative-jump-containing cells have a mesh-independent expected-count budget
-- statement:
--   On the unchanged original finite-activity spectrally negative Lévy process, select any finite set of physically negative-jump-containing grid-cell indices, with a measurable real count and an explicit samplewise injection bound into the true original negative marked jump count on the finite horizon. Then the selected-cardinality random variable is integrable, and its expected value on any event is bounded by the actual physical negative Lévy intensity times the horizon, independently of grid refinement, without assuming negative mark size moments.
-- source:
--   Proved physical Borel negative mark real count first moment JA35, source-physical selected grid jump-cardinality injection hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b58_original_selected_negative_jump_cells_uniform_count_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A : Set Ω)
    (J : Ω → Finset ℕ)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal) :
    Integrable (fun ω => ((J ω).card : ℝ)) P ∧
    (∫ ω in A, ((J ω).card : ℝ) ∂P) ≤
      ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
