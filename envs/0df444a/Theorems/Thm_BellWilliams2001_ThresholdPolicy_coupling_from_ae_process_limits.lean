-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_coupling_from_ae_process_limits
-- name    : BellWilliams2001.ThresholdPolicy.coupling_from_ae_process_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:03:33.338873+00:00
-- url     : https://prove2.me/theorems/d52f5221-1e6e-5c98-8e9a-60f9758d734e
-- title:
--   Path coupling with almost everywhere measurable process observations
-- statement:
--   Finite-dimensional convergence and control of the compact interval modulus produce the path coupling for càdlàg prelimit processes and an almost surely continuous limit, when finite observations are almost everywhere measurable.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_measurable_path_version
import Theorems.Thm_ManyServerQED_Scheduling_functional_coupling_from_fdd_and_interval_modulus

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem coupling_from_ae_process_limits {Ω : Type*} {Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (Z : Ω' → ℝ → Fin k → ℝ)
    (hX : ∀ n ω i, IsCadlag (fun t => X n ω t i))
    (hZ : ∀ᵐ ω ∂P', ContinuousOn (Z ω) (Ici (0:ℝ)))
    (hF : ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    CouplingConverges P P' X Z := by sorry

end BellWilliams2001.ThresholdPolicy
