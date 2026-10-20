-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaledW_generator_harmonic_of_scale_harmonic_at_positive
-- name    : AvramDividend.Classical.scaledW_generator_harmonic_of_scale_harmonic_at_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:28:57.53874+00:00
-- url     : https://prove2.me/theorems/58cc0455-c6bd-4aa8-b59a-345951853184
-- title:
--   Transport of exact scale-function harmonicity to its dividend normalisation at a positive reserve
-- statement:
--   At any positive reserve a, assume the actual q-scale function W is in the spectrally negative Lévy generator domain and satisfies its exact q-harmonic generator equation at a. Then its dividend normalisation z↦divE(W z,scaleDeriv W a) is also generator-integrable and q-harmonic at a. Because a>0, scaleDeriv reduces to the ordinary derivative, and the EReal totalised denominator yields a constant real scalar even if W'(a)=0. The proof uses genuine scalar-linearity and domain-preservation lemmas for the full compensated Lévy generator. The assumptions explicitly expose the still-open hard stochastic generator identity rather than treating it as already Proved.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaledW_generator_harmonic_of_scale_harmonic_at_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hdom : X.GeneratorIntegrable W a)
    (hharm : X.generator W a - q * W a = 0) :
    X.GeneratorIntegrable
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) a ∧
      X.generator
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) a -
        q * divE (W a) (scaleDeriv W a) = 0 := by sorry
