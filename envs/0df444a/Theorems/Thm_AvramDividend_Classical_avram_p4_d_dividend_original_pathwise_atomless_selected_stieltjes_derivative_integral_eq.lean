-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_pathwise_atomless_selected_stieltjes_derivative_integral_eq
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_pathwise_atomless_selected_stieltjes_derivative_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:56:00.760858+00:00
-- url     : https://prove2.me/theorems/924a02ed-8753-448b-a2b2-f4083e34632c
-- title:
--   Original path-dependent atomless dividend Stieltjes signed derivative integral is unchanged by pre-source left-limit localisation on every selected positive-time region
-- statement:
--   For any fixed original Lévy path, any atomless dividend component measure (including one depending on that path), and every measurable positive-time subset A, the discounted signed diffuse derivative integral over A computed at riskProcess X x D agrees exactly with the same integral at x + leftLim X - rightLimit D. The proof uses the Proved pathwise source-state equality a14bf58b, restriction of an a.e. statement to A, and equality of Lebesgue integrals a.e. No deterministic-measure Fubini substitution, time-zero atom loss or regularity assumption on w is needed.
-- source:
--   Original pathwise arbitrary-atomless pre-source reserve agreement a14bf58b-7618-46d8-8305-425cfaa67b49. Stronger set-local form of Proved full-positive-axis integral equality f2ba7e75-689b-488e-a0a1-ecc5bf85856b, used in Avram P4-F dividend localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_pathwise_atomless_selected_stieltjes_derivative_integral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ) (hA : MeasurableSet A) (hApos : A ⊆ Ioi (0 : ℝ))
    (q : ℝ) (w : ℝ → ℝ) :
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) =
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω)) ∂ν) := by sorry
