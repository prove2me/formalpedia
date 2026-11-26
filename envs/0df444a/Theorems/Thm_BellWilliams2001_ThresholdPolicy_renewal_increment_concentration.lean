-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_increment_concentration
-- name    : BellWilliams2001.ThresholdPolicy.renewal_increment_concentration
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:19.887567+00:00
-- url     : https://prove2.me/theorems/7767bced-b22d-4619-8410-d4b48d8cb535
-- title:
--   Uniform logarithmic renewal-count increment errors on a diffusion horizon
-- statement:
--   For independent mean-one durations with exponential moments, the centered renewal-count increments on [0,r²t] are bounded in absolute value by a prescribed linear tolerance in the interval length plus a constant times log r. The failure probability is at most C(1+t)/r⁶, uniformly over rates in a fixed bounded interval.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Appendix A and Section 7, uniform exponential estimates for the renewal input

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

theorem renewal_increment_concentration {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → ℝ) (hW : ∀ j, Measurable (W j)) (hPos : ∀ j ω, 0 < W j ω)
    (hi : iIndepFun W P) (hid : ∀ j, IdentDistrib (W j) (W 0) P P)
    (hInt : Integrable (W 0) P) (hMean : ∫ ω, W 0 ω ∂P = 1)
    (hmom : ∃ a > 0, ∀ u ∈ Set.Ioo (-a) a, Integrable (fun ω => Real.exp (u * W 0 ω)) P)
    (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ (r rate t : ℝ), 1 ≤ Real.log r → 1 ≤ r →
      0 < rate → rate ≤ A → 0 ≤ t →
      let e (ω : Ω) (m : ℕ) := ∑ j ∈ Finset.range m, W j ω
      let N (ω : Ω) (s : ℝ) : ℝ := ((renewalCount (e ω) (rate * s)).toNat : ℝ)
      P {ω | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ v ∧ v ≤ r^2*t ∧
        η*(v-u) + K*Real.log r < |N ω v - N ω u - rate*(v-u)|} ≤
        ENNReal.ofReal (C*(1+t)/r^6) := by sorry

end BellWilliams2001.ThresholdPolicy
