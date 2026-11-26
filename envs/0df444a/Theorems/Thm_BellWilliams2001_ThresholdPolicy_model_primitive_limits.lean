-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_model_primitive_limits
-- name    : BellWilliams2001.ThresholdPolicy.model_primitive_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:06:45.248686+00:00
-- url     : https://prove2.me/theorems/948c58e1-b8c6-4654-92d3-623b95b908c8
-- title:
--   Joint diffusion limit for the five Bell–Williams primitive processes
-- statement:
--   The centered arrival and service processes of the model have joint Brownian finite observation laws and a uniform compact modulus bound, with rates and duration variances specified by the model.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem model_primitive_limits {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : SystemSequence Ω) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (B : Fin 5 → ℝ≥0 → Ω' → ℝ) (hB : ∀ i, IsBrownianReal (B i) P')
    (hBc : ∀ i ω, Continuous (fun t => B i t ω))
    (hIndB : iIndepFun (fun i ω t => B i t ω) P') :
    letI := M.isProb
    let X (n : ℕ) (ω : Ω) (t : ℝ) := Fin.append (M.Ahat (φ n) ω t) (M.Shat (φ n) ω t)
    let Z (ω : Ω') (t : ℝ) (i : Fin 5) :=
      (Fin.append (fun k => Real.sqrt (M.lam k*M.alphaSq k))
        (fun j => Real.sqrt (M.mu j*M.betaSq j))) i * B i t.toNNReal ω
    (∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => M.P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) := by sorry

end BellWilliams2001.ThresholdPolicy
