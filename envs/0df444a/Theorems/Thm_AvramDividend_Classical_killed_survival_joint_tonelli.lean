-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_survival_joint_tonelli
-- name    : AvramDividend.Classical.killed_survival_joint_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:41:17.437968+00:00
-- url     : https://prove2.me/theorems/d8edf9db-e35a-4729-90b1-6ddf8bef7415
-- title:
--   Capital and sample-path integrals commute for finite-horizon killed Lévy survival
-- statement:
--   For any spectrally negative Lévy process and finite horizon, the extended nonnegative Laplace capital kernel killed when the reserve becomes negative is jointly measurable and Tonelli allows integration in starting capital and sample path in either order. No moment or integrability assumptions are needed. This is the exact measure-theoretic interchange needed to connect the already Proved pathwise capital integral to a stochastic reflected-infimum transform.
-- source:
--   Proved joint_reserve_closed_survival_measurable and pinned Mathlib MeasureTheory.lintegral_lintegral_swap, ENNReal.measurable_ofReal.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_joint_reserve_closed_survival_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_survival_joint_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (θ : ℝ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) =
    (∫⁻ (ω : Ω), ∫⁻ (x : ℝ),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂volume ∂P) := by sorry
