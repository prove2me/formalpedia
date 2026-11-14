-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_weak_solution_from_girsanov_shift
-- name    : AppliedSDE.SarkkaSolin.weak_solution_from_girsanov_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:48:17.251687+00:00
-- url     : https://prove2.me/theorems/d66e1876-7338-41e2-8f20-92f3471be557
-- title:
--   Weak SDE solution from a Girsanov-shifted Brownian motion
-- statement:
--   Assume W is Brownian under P and let Q be the measure obtained from a suitable Girsanov density. Given a drift f, a deterministic initial state x0, and a transformed process B_t=W_t−∫_0^t f(x0+W_s,s)ds which is Brownian under Q, define X_t=x0+W_t. Then X_0=x0 and X satisfies the integral stochastic equation X_t=x0+∫_0^t f(X_s,s)ds+B_t under Q. The hypothesis that B is Brownian under Q is the conclusion of the preceding Girsanov theorem and is explicitly separated from this corollary. The statement forms a non-vacuous weak-solution construction with pointwise pathwise equality.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   X_t=x_0+\int_0^t f(X_s,s)\,\mathrm ds+B_t
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (2019), Corollary 7.9, equations (7.50)–(7.54), printed pp. 108–109. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.weak_solution_from_girsanov_shift
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
    (∀ ω : Ω, X 0 ω = x₀) ∧
    (∀ (t : ℝ≥0) (ω : Ω),
      X t ω = x₀ + (∫ s in (0 : ℝ)..(t : ℝ),
        f (X s ω) s) + shifted t ω) := by
  sorry
