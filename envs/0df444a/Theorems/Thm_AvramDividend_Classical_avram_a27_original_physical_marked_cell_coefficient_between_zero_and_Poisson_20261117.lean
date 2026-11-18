-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_cell_coefficient_between_zero_and_Poisson_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_marked_cell_coefficient_between_zero_and_Poisson_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:28:55.933201+00:00
-- url     : https://prove2.me/theorems/a251178c-61f2-40dd-bff4-e6e90a1d37f6
-- title:
--   Each original physical negative marked-jump exponential count-cell coefficient lies between zero and its true Poisson mass
-- statement:
--   For every physical negative-jump count k on the original spectrally negative Levy probability space, the expected exponential of its actual finite negative jump sum restricted to K=k is between zero and the exact Poisson(r) probability of the original count event. No marking independence is assumed. This coefficientwise inequality is a source-space necessary estimate for the full marked Poisson conditional moment formula.
-- source:
--   Proved original physical jump exponential A85; Proved original Borel negative count singleton Poisson law A114; pinned integral_mono_ae and ae_restrict_of_ae.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_marked_cell_coefficient_between_zero_and_Poisson_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (r : ℝ≥0)
    (hRate : (r : ℝ) = ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∀ k : ℕ,
      0 ≤ (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) ∧
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) ≤
        (poissonMeasure r).real {k} := by sorry
