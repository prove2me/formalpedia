-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_reflected_finite_observations_from_coupling
-- name    : BellWilliams2001.ThresholdPolicy.reflected_finite_observations_from_coupling
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:06:43.446642+00:00
-- url     : https://prove2.me/theorems/6f5e76fe-9476-5ec3-98e7-e0521c4102e7
-- title:
--   Finite observation limits for a coupled reflected process
-- statement:
--   A compact-uniform scalar path coupling to a continuous limit gives finite-dimensional convergence of the reflected input and its regulator after multiplying by convergent coefficients.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem reflected_finite_observations_from_coupling {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ → ℝ) (Z : Ω' → ℝ → ℝ)
    (hX : ∀ n ω, IsCadlag (X n ω))
    (hXm : ∀ n t, 0 ≤ t → AEMeasurable (fun ω => X n ω t) P)
    (hZ : ∀ᵐ ω ∂P', Continuous (Z ω))
    (hCouple : CouplingConverges P P' (fun n ω t => ![X n ω t]) (fun ω t => ![Z ω t]))
    (a b : ℕ → ℝ) (A B : ℝ) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    let R (x : ℝ → ℝ) (t : ℝ) := x t-⨅ s : Icc (0:ℝ) t, x s
    let V (x : ℝ → ℝ) (t : ℝ) := -(⨅ s : Icc (0:ℝ) t, x s)
    let Y (n : ℕ) (ω : Ω) (t : ℝ) := ![0,a n*R (X n ω) t,0,b n*V (X n ω) t]
    let W (ω : Ω') (t : ℝ) := ![0,A*R (Z ω) t,0,B*V (Z ω) t]
    ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop
        (fun ω j => W ω (τ j)) (fun _ => P) P' := by sorry

end BellWilliams2001.ThresholdPolicy
