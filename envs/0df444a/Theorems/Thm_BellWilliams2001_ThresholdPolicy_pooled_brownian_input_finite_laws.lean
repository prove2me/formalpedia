-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_pooled_brownian_input_finite_laws
-- name    : BellWilliams2001.ThresholdPolicy.pooled_brownian_input_finite_laws
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:06:38.995933+00:00
-- url     : https://prove2.me/theorems/0488a6b4-72f7-5fc2-9d20-85234eb30cbb
-- title:
--   The five primitive Brownian motions give the projected workload law
-- statement:
--   The projected weighted Brownian primitive paths at the critical service clocks have the same finite observation law as the pooled Brownian input in the control problem.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem pooled_brownian_input_finite_laws {Ω Ω₁ Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (M : SystemSequence Ω) (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (C : Fin 5 → ℝ≥0 → Ω₁ → ℝ) (hC : ∀ i, IsBrownianReal (C i) P₁)
    (hCm : ∀ i t, Measurable (C i t)) (hCI : iIndepFun (fun i ω t => C i t ω) P₁)
    (P₂ : Measure Ω₂) (B : Fin 2 → ℝ≥0 → Ω₂ → ℝ) (hB : IsBrownianPair P₂ B)
    (q : ℕ) (τ : Fin q → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
    let ρ : Fin 5 → ℝ := ![1,1,1,(M.lam 0-M.mu 0)/M.mu 1,M.lam 1/M.mu 2]
    let y := M.yvec 1
    let a : Fin 5 → ℝ := ![1,y,-1,-1,-y]
    let C₀ := Fin.append (fun k => Real.sqrt (M.lam k*M.alphaSq k))
      (fun j => Real.sqrt (M.mu j*M.betaSq j))
    IdentDistrib (fun ω j => ![(∑ i, a i*C₀ i*C i (ρ i*τ j).toNNReal ω) +
      (M.theta 0+y*M.theta 1)*τ j])
      (fun ω j => ![∑ i,M.yvec i*M.Xtilde B ω (τ j) i]) P₁ P₂ := by sorry

end BellWilliams2001.ThresholdPolicy
