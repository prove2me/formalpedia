-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel
-- name    : AvramDividend.Classical.chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:18:04.001977+00:00
-- url     : https://prove2.me/theorems/8c2d238f-f358-4391-a0b2-75633a64a865
-- title:
--   Scalar killed q-scale renewal implies the shifted random-reserve expectation
-- statement:
--   Assuming scalar fixed-time killed-scale renewal for each initial reserve, the full killed discounted q-scale expectation for a measurable random reserve at any past time equals its initial scale expectation. This combines continuous-time killed Markov–Tonelli factorisation with integration of the scalar identity.
-- source:
--   Proved chat04_true_killed_scale_markov_tonelli_grid_kernel; isolates scalar renewal prerequisite for Open killed discounted scale martingale.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_markov_tonelli_grid_kernel

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_scale_shifted_expectation_of_scalar_renewal_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hScalar : ∀ h : ℝ,
      (∫⁻ y,
        (if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + y (τ j)
         then ENNReal.ofReal
           (Real.exp (-(q * (T : ℝ))) * W (h + y T))
         else (0 : ℝ≥0∞))
        ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)) =
      ENNReal.ofReal (W h)) :
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ T →
          0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
      then ENNReal.ofReal
        (Real.exp (-(q * (T : ℝ))) *
          W (H ω + (X.X (s + T) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ENNReal.ofReal (W h) ∂(Measure.map H P) := by sorry
