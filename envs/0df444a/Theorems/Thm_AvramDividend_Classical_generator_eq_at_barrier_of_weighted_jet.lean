-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_eq_at_barrier_of_weighted_jet
-- name    : AvramDividend.Classical.generator_eq_at_barrier_of_weighted_jet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:27:37.617991+00:00
-- url     : https://prove2.me/theorems/89017564-7fe6-46df-aed3-1d4a4fde5969
-- title:
--   Generator locality at a barrier with Gaussian-weighted second derivative matching
-- statement:
--   At a barrier a, the generator Γ of a spectrally negative Lévy process depends on values at and below a, on the first derivative at a, and only on the Gaussian-weighted second derivative σ² f''(a). If two functions agree on (-∞,a], have identical first derivatives and identical σ²-weighted second derivatives at a, then their generator integrability and Γ values agree exactly at the barrier. In particular, for bounded variation σ=0 no second-derivative condition is needed, while the Gaussian case requires matching second derivatives. This sharpens the endpoint locality lemma and is directly applicable to the BV/C2 split in the HJB at c*.
-- source:
--   Direct algebraic consequence of the extended generator formula in Avram, Palmowski and Pistorius (2007), Section 5.1; the Lévy measure is supported on negative jumps and the Gaussian term has coefficient σ²/2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem generator_eq_at_barrier_of_weighted_jet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (f g : ℝ → ℝ) (a : ℝ)
    (hfg : ∀ z : ℝ, z ≤ a → f z = g z)
    (hder : deriv f a = deriv g a)
    (hweighted :
      X.σ ^ 2 * iteratedDeriv 2 f a =
        X.σ ^ 2 * iteratedDeriv 2 g a) :
    (X.GeneratorIntegrable f a ↔ X.GeneratorIntegrable g a) ∧
      X.generator f a = X.generator g a := by
  sorry
end AvramDividend.Classical
