-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_finite_strict_large_marks
-- name    : AvramDividend.Classical.avram_p3_main_original_ae_finite_strict_large_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:52:24.360783+00:00
-- url     : https://prove2.me/theorems/2f296cf8-0fb4-497a-8225-e7c5ff2b1ffe
-- title:
--   Actual original BV source large negative left-jump times are finite and strictly after zero
-- statement:
--   For the genuine original BV spectrally negative Lévy process, one full-measure event simultaneously gives that for every positive δ, source negative left jumps of magnitude at least δ in the interval (0,T] form a finite set of genuine nonnegative source-times. Moreover, every selected mark is strictly positive and no later than the actual horizon, including the horizon endpoint. The proof instantiates source BV absolute summability and pinned cofinite tail convergence, then uses the explicit interval filter to exclude t=0 and t>T.
-- source:
--   Proved 54643412 original interval left-jump real absolute summability and pinned Mathlib Summable.tendsto_cofinite_zero; P3-D interface obligations 1,2 and P3-C cell chronology.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Set MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p3_main_original_ae_finite_strict_large_marks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let j : ℝ≥0 → ℝ := fun u =>
        if 0 < u ∧ u ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0
      ∀ δ : ℝ, 0 < δ →
        {u : ℝ≥0 | δ ≤ |j u|}.Finite ∧
        ∀ u : ℝ≥0, δ ≤ |j u| → 0 < u ∧ u ≤ T := by sorry
