-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_inverse_approximation_in_probability
-- name    : BellWilliams2001.ThresholdPolicy.renewal_inverse_approximation_in_probability
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:37:54.137187+00:00
-- url     : https://prove2.me/theorems/7dbea0c4-48f1-4483-8e9e-3a16b2425aea
-- title:
--   Inversion of renewal epochs approximates the negative scaled epoch walk
-- statement:
--   For a cofinal sequence of integer scaling parameters, control of the epoch walk by weak convergence in continuous path space gives a uniform-in-probability approximation of the normalized centered renewal count by the negative epoch walk on any fixed observation horizon.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Set DurrettProbability
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem renewal_inverse_approximation_in_probability {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (h : TendstoInDistribution Y atTop Z (fun _ => P) P')
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (q J : ℝ) (hq : 0 < q) (hJ : 0 < J)
    (e : ℕ → Ω → ℕ → ℝ) (he : ∀ n ω, StrictMono (e n ω)) (he0 : ∀ n ω, e n ω 0 = 0)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (T : ℝ) (hT : 0 ≤ T)
    (hH : ∀ᶠ n in atTop, aN n*T+3 ≤ J)
    (hg : ∀ (n : ℕ), 1 ≤ m n → ∀ ω (j : ℕ), (j:ℝ)/m n ≤ J →
      q*Y n ω (projIcc 0 1 zero_le_one (((j:ℝ)/m n)/J)) =
        (e n ω j-j)/Real.sqrt (m n)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
        ε ≤ |(((renewalCount (e n ω) ((m n:ℝ)*aN n*t)).toNat:ℝ) - (m n:ℝ)*aN n*t)/Real.sqrt (m n) +
          q*Y n ω (projIcc 0 1 zero_le_one (aN n*t/J))|}) atTop (𝓝 0) := by sorry

end BellWilliams2001.ThresholdPolicy
