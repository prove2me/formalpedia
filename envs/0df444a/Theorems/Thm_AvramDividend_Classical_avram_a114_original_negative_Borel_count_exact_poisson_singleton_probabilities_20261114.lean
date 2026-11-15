-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
-- name    : AvramDividend.Classical.avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T19:10:58.251806+00:00
-- url     : https://prove2.me/theorems/a8c62c49-8428-4b81-89c4-d6f51c329a09
-- title:
--   Original physical negative Borel jump count has exact Poisson singleton event probabilities at the source rate
-- statement:
--   For any original spectrally negative Lévy process with finite negative activity and measurable integer-valued representative of the actual physical Borel marked jump count, show that every exact count-k event has probability given by the Poisson law of rate T ν(B). This is the full source Poisson event-probability calculation. It isolates the distributional part from the separately Proved original count measurability and integer realisation. No auxiliary Lévy probability space or zero Gaussian assumption.
-- source:
--   Independent-increment original Lévy jump counting process characterisation; pathwise marked source count via Proved A20 nat realisation, A90 conditional void probabilities and measured original finite-grid jumps. Full count-k probabilities are the remaining stochastic target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    ∀ k : ℕ, P {ω : Ω | K ω = k} = poissonMeasure r {k} := by sorry
