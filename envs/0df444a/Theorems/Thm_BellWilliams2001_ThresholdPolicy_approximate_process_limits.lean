-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_approximate_process_limits
-- name    : BellWilliams2001.ThresholdPolicy.approximate_process_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:06:33.131944+00:00
-- url     : https://prove2.me/theorems/fd1961b1-1c42-4b37-a545-e59bd41b62fd
-- title:
--   Stability of process limits under uniform small perturbations
-- statement:
--   A sequence of processes uniformly close in probability on each compact time interval to a sequence with a finite-observation limit and asymptotic modulus bound shares that limit and bound.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem approximate_process_limits {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X Y : ℕ → Ω → ℝ → Fin k → ℝ) (Z : Ω' → ℝ → Fin k → ℝ)
    (hY : ∀ n t, 0 ≤ t → AEMeasurable (fun ω => Y n ω t) P)
    (hF : ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η)
    (hA : ∀ (T : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), ε ≤ ‖Y n ω t-X n ω t‖}) atTop (𝓝 0)) :
    (∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖Y n ω s-Y n ω t‖} ≤ ENNReal.ofReal η) := by sorry

end BellWilliams2001.ThresholdPolicy
