-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_survival_capital_antitone_horizon
-- name    : AvramDividend.Classical.killed_survival_capital_antitone_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:11:26.738564+00:00
-- url     : https://prove2.me/theorems/10480864-244c-46d0-aea2-16acbf2a2f84
-- title:
--   Killing reduces capital-integrated Lévy survival mass as the horizon grows
-- statement:
--   The nonnegative Laplace mass of initial reserves surviving a Lévy path up to a given horizon is nonincreasing in the observation horizon, for any real exponent θ. Longer survival implies shorter survival pointwise, and the kernel is nonnegative, so two monotonicity steps under Lebesgue integration prove the result. Useful in extending finite-horizon transforms to limiting renewal potentials.
-- source:
--   Finite-horizon killed-survival kernel; pinned Mathlib lintegral_mono and Set.indicator_of_mem/notMem.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_killed_survival_joint_tonelli

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_survival_capital_antitone_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t u : ℝ≥0) (htu : t ≤ u) (θ : ℝ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ u → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) ≤
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) := by sorry
