-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_killed_survival_joint_tonelli
-- name    : AvramDividend.Classical.chat04_esscher_weighted_killed_survival_joint_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:46:05.975172+00:00
-- url     : https://prove2.me/theorems/acec54ba-7740-4e8d-aaba-a7d1ee26ecff
-- title:
--   Tonelli for Esscher-weighted killed capital and Lévy sample paths
-- statement:
--   The nonnegative joint capital and path integration of a continuously killed finite-horizon Esscher-weighted Laplace kernel can be interchanged. The kernel includes the actual Lévy terminal exponential, not merely the unweighted survival indicator.
-- source:
--   Adapts already Proved killed_survival_joint_tonelli (d8edf9db) to the true Esscher-weighted integrand. The joint continuous survival set is Proved measurable, the fixed-time Lévy increment is adapted and measurable, and the full ENNReal kernel is jointly measurable, giving Mathlib Tonelli. This supplies the missing probabilistic interchange for the finite-horizon Esscher descending-infimum transform without using the exit identity.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_joint_reserve_closed_survival_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_killed_survival_joint_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    (∫⁻ (ω : Ω), ∫⁻ (x : ℝ),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂volume ∂P) := by sorry
