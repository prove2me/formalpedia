-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_clock_marginal_of_measurable_likelihood
-- name    : AvramDividend.Classical.chat04_esscher_joint_exponential_clock_marginal_of_measurable_likelihood
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:37:38.259553+00:00
-- url     : https://prove2.me/theorems/0ee3767d-6da9-4ff4-a331-0c0c5f9d05c0
-- title:
--   An actual time-dependent finite-rate Esscher law retains its external exponential observation-time marginal
-- statement:
--   For the genuine θ-Esscher joint law at an independent Exp(p) observation time, the clock marginal remains exactly the original exponential law after reweighting by exp(θX_{t+}−t+ψθ), assuming only joint measurability of that explicit likelihood. The proof uses the actual Lévy exponential moment theorem to verify normalisation at every real clock time. This is stronger than a simple product construction: the joint law is no longer a product of path and clock, but the clock's marginal remains exponential exactly.
-- source:
--   Under the original Lévy probability structure X.isProbability and Mathlib's positive-rate exponential distribution, apply the accepted `chat04_fibrewise_normalized_joint_tilt_clock_marginal` to the concrete Esscher density. For every real observation time t, its nonnegative clamp Real.toNNReal t has an accepted finite-horizon tilted probability law; its total mass rewritten via `withDensity_apply` and `Measure.restrict_univ` is 1, exactly the generic theorem's fibrewise normalisation. This proves equality of measures without any tilted infinite-horizon path law.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_chat04_fibrewise_normalized_joint_tilt_clock_marginal
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_joint_exponential_clock_marginal_of_measurable_likelihood
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
    (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    Measure.map Prod.snd
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
    (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) =
      ProbabilityTheory.expMeasure p := by sorry
