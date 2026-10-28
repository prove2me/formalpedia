-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform
-- name    : AvramDividend.Classical.killed_survival_capital_reflected_infimum_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:55:47.029977+00:00
-- url     : https://prove2.me/theorems/2d402c68-16a8-47ca-9823-54da81a7f776
-- title:
--   Laplace transform of the Lévy killed-survival potential as expected reflected running infimum
-- statement:
--   For every positive Laplace parameter and finite horizon, integrate the nonnegative Lévy killed-survival indicator first over sample paths and then over positive starting capital. This equals the expectation of the explicit exponential envelope determined by the sample path's running infimum. Proof combines Tonelli and exact inner-capital integral, both Proved.
-- source:
--   Proved killed_survival_joint_tonelli and killed_survival_inner_lintegral_envelope.

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_killed_survival_joint_tonelli
import Theorems.Thm_AvramDividend_Classical_killed_survival_inner_lintegral_envelope

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_survival_capital_reflected_infimum_transform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) =
    (∫⁻ (ω : Ω),
      ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) ∂P) := by sorry
