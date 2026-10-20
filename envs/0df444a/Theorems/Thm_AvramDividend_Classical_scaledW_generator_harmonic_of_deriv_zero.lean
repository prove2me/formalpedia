-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaledW_generator_harmonic_of_deriv_zero
-- name    : AvramDividend.Classical.scaledW_generator_harmonic_of_deriv_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:13:32.787314+00:00
-- url     : https://prove2.me/theorems/3de4f31c-c5b7-4e89-9f91-2b1943841483
-- title:
--   Totalised zero-derivative denominator gives a zero harmonic scaled value
-- statement:
--   For any real scale candidate W and positive evaluation point a where its ordinary derivative is zero, the exact Formalpedia normalisation z↦divE(W z,scaleDeriv W a) is the identically zero function. Because the divE definition uses real totalised division, even its zero denominator produces zero. Hence the full spectrally negative Lévy generator jump term is integrable, and the normalised value is exactly q-harmonic at a for every real q, regardless of unproved scale-function stochastic harmonicity. This resolves the zero-denominator branch in the positive-cstar scaled-generator proof, rather than silently dividing by an assumed nonzero derivative.

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaledW_generator_harmonic_of_deriv_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ)
    (ha : 0 < a) (hder : deriv W a = 0) :
    X.GeneratorIntegrable
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) a ∧
      X.generator
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) a -
        q * divE (W a) (scaleDeriv W a) = 0 := by sorry
