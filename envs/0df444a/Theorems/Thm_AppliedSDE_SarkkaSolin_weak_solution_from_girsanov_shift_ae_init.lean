-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_weak_solution_from_girsanov_shift_ae_init
-- name    : AppliedSDE.SarkkaSolin.weak_solution_from_girsanov_shift_ae_init
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:29:12.151201+00:00
-- url     : https://prove2.me/theorems/27e57115-87d0-41f2-ba62-65302f7d7d70
-- title:
--   Girsanov shifted Brownian process gives the weak SDE identity, with almost-sure initial value
-- statement:
--   Given a Brownian motion W under P and a tilted Q for which W minus the integrated drift is Brownian, X_t = x0 + W_t satisfies the SDE integral identity pathwise and the initial condition almost surely under P. The original public weak_solution_from_girsanov_shift incorrectly demanded W_0=0 at every outcome while the BrownianMotion structure provides W.initial_zero only almost surely; this published variant preserves the correct measure-theoretic quantifier.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Girsanov weak-solution construction.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.weak_solution_from_girsanov_shift_ae_init
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (x₀ : ℝ) (f : ℝ → ℝ → ℝ)
    (hInt : ∀ (t : ℝ≥0) (ω : Ω), IntegrableOn
      (fun s : ℝ => f (x₀ + W.W s ω) s)
      (Set.Icc (0 : ℝ) (t : ℝ)))
    (hBrownian : IsBrownianReal
      (fun (t : ℝ≥0) (ω : Ω) =>
        W.W (t : ℝ) ω -
          ∫ s in (0 : ℝ)..(t : ℝ), f (x₀ + W.W s ω) s) Q) :
    let X : ℝ → Ω → ℝ := fun t ω => x₀ + W.W t ω
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω -
        ∫ s in (0 : ℝ)..(t : ℝ), f (X s ω) s
    (∀ᵐ ω ∂P, X 0 ω = x₀) ∧
    (∀ (t : ℝ≥0) (ω : Ω),
      X t ω = x₀ + (∫ s in (0 : ℝ)..(t : ℝ),
        f (X s ω) s) + shifted t ω) := by
  sorry
