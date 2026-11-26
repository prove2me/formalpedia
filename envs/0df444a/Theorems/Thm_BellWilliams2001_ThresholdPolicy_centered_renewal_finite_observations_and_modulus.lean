-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_centered_renewal_finite_observations_and_modulus
-- name    : BellWilliams2001.ThresholdPolicy.centered_renewal_finite_observations_and_modulus
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:03:37.099789+00:00
-- url     : https://prove2.me/theorems/950b7cff-d34f-4cd1-86f3-019a85552290
-- title:
--   Diffusion-scale finite laws and compact modulus of a renewal count
-- statement:
--   A renewal counting process driven by iid positive mean-one durations has centered finite-dimensional limits given by a scaled Brownian motion. Its maximum and interval modulus are tight on each compact horizon. The clock and cofinal integer diffusion scales may vary.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_epoch_donsker
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_inverse_approximation_in_probability
import Theorems.Thm_ManyServerQED_Scheduling_uniform_path_approximation_transfers_norm_and_modulus_bounds
import Theorems.Thm_ManyServerQED_Scheduling_brownian_weighted_finite_observation_law

open MeasureTheory ProbabilityTheory Filter Topology Set DurrettProbability
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem centered_renewal_finite_observations_and_modulus {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (V : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (V j)) (hind : iIndepFun V P)
    (hident : ∀ j, IdentDistrib (V j) (V 0) P P) (hLp : MemLp (V 0) 2 P)
    (hmean : ∫ ω, V 0 ω ∂P = 1) (hpos : ∀ j ω, 0 < V j ω)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (a : ℝ) (ha : 0 < a)
    (halim : Tendsto aN atTop (𝓝 a))
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    let X (n : ℕ) (ω : Ω) (t : ℝ) :=
      (((renewalCount (fun j => ∑ i ∈ Finset.range j, V i ω) ((m n:ℝ)*aN n*t)).toNat:ℝ)
        - (m n:ℝ)*aN n*t) / Real.sqrt (m n)
    let Z (ω : Ω') (t : ℝ) := Real.sqrt (a*variance (V 0) P) * B t.toNNReal ω
    (∀ (k : ℕ) (τ : Fin k → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P') ∧
    (∀ T ε η : ℝ, 0 ≤ T → 0 < ε → 0 < η → ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | (∃ t ∈ Icc (0:ℝ) T, A ≤ |X n ω t|) ∨
        ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
          ε ≤ |X n ω s-X n ω t|} ≤ ENNReal.ofReal η) := by sorry

end BellWilliams2001.ThresholdPolicy
