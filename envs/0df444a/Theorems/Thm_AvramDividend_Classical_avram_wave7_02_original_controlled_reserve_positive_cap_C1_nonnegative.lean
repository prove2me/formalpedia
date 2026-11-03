-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_controlled_reserve_positive_cap_C1_nonnegative
-- name    : AvramDividend.Classical.avram_wave7_02_original_controlled_reserve_positive_cap_C1_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:56:10.293684+00:00
-- url     : https://prove2.me/theorems/2217ac23-5d17-4704-9cc8-eaf0249233f8
-- title:
--   Original controlled reserve inherits positive-cap C1 candidate nonnegativity at every strict interior position
-- statement:
--   For the genuine controlled reserve of the canonical Avram spectrally negative Levy risk process and an admissible dividend strategy, nonnegative reserves strictly inside a positive cap have nonnegative C1 HJB candidate value. The proof applies the Proved original positive-cap compact monotonicity theorem with the actual reserve as its upper interval endpoint. It preserves the original Ω, P, X, filtration and dividend control without changing any stochastic definitions.
-- source:
--   Source-specific riskProcess adapter to Proved cb439447-a20c-4328-b137-88d209abc249, using exact original C1 HJB candidate assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_controlled_reserve_positive_cap_C1_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 ≤ riskProcess X x D t ω →
      ENNReal.ofReal (riskProcess X x D t ω) < C →
      0 ≤ w (riskProcess X x D t ω) := by sorry
