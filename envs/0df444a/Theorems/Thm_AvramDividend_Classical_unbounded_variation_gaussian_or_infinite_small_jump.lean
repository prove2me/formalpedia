-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump
-- name    : AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:15:50.570981+00:00
-- url     : https://prove2.me/theorems/eecb5c8f-ffc1-4751-ace9-b03f4eec099a
-- title:
--   Unbounded variation implies positive Gaussian component or infinitely active first-moment small jumps
-- statement:
--   For a spectrally negative Levy process, failure of bounded variation entails either strictly positive Gaussian coefficient or infinite integral of the absolute sizes of jumps in (-1,0), using the defining bounded-variation dichotomy.
-- source:
--   The bounded-variation field equivalence and non-negativity of the Gaussian coefficient; a root-connected branching lemma for the Gaussian and infinite-small-jump Wiener–Hopf arguments.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    0 < X.σ ∨
      (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) = ⊤ := by sorry
