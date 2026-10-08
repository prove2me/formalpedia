-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_eq_at_barrier_of_agree_below_and_jet
-- name    : AvramDividend.Classical.generator_eq_at_barrier_of_agree_below_and_jet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:22:09.414052+00:00
-- url     : https://prove2.me/theorems/e7c7c5e1-b856-4338-8b8d-5b30ba1fb3df
-- title:
--   Spectrally negative generator locality at a barrier with matching first and second derivatives
-- statement:
--   At the boundary a of a spectrally negative generator, if f and g agree everywhere at and below a and their first and second derivatives agree at a, then both the generator jump-integrability predicate and generator values agree at a. The Lévy measure in Γ is supported on y<0, where a+y<a and the jump integrands are pointwise equal. The drift and Gaussian parts agree by the derivative hypotheses. This fills an endpoint locality gap not covered by the already proved strict-interior generator_eq_of_agree_below lemma, and supports the HJB equality exactly at c*. Purely algebraic and measure-theoretic, independent of the fluctuation assumptions.
-- source:
--   Source-neutral consequence of the formal spectrally negative Lévy generator in Avram, Palmowski and Pistorius (2007), Section 5.1. Endpoint counterpart of generator_eq_of_agree_below.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem generator_eq_at_barrier_of_agree_below_and_jet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (f g : ℝ → ℝ) (a : ℝ)
    (hfg : ∀ z : ℝ, z ≤ a → f z = g z)
    (hder : deriv f a = deriv g a)
    (hsecond : iteratedDeriv 2 f a = iteratedDeriv 2 g a) :
    (X.GeneratorIntegrable f a ↔ X.GeneratorIntegrable g a) ∧
      X.generator f a = X.generator g a := by
  sorry
end AvramDividend.Classical
