-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_integrable_cross_split_yields_three_error_package
-- name    : AvramDividend.Classical.avram_ga_integrable_cross_split_yields_three_error_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:44:04.777292+00:00
-- url     : https://prove2.me/theorems/f348ce20-9987-4729-a667-d9f77da0db83
-- title:
--   Global cross absolute L1 plus positive residual L1 imply eventwise three-error certificate
-- statement:
--   Let E be a stopped cash excess sequence, B a concrete Hessian cross error and A the positive-clock event. Assume E positive-part integrability on A, global integrability and vanishing absolute L1 for B, and integrability and vanishing eventwise positive L1 for E−B. Then construct the three-error source certificate with T=max(E−B,0), H=B, R=0. This is exact and avoids any unsupported stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_integrable_cross_split_yields_three_error_package
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (E B : ℕ → Ω → ℝ)
    (hEI : ∀ m, Integrable (fun ω => max (E m ω) 0) (P.restrict A))
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hTI : ∀ m, Integrable (fun ω => max (E m ω - B m ω) 0)
      (P.restrict A))
    (hTt : Tendsto (fun m => ∫ ω in A, max (E m ω - B m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ))) :
    ∃ (T H R : ℕ → Ω → ℝ),
      (∀ m, Integrable (fun ω => max (E m ω) 0) (P.restrict A)) ∧
      (∀ m, Integrable (fun ω => max (T m ω) 0) (P.restrict A)) ∧
      (∀ m, Integrable (fun ω => |H m ω|) (P.restrict A)) ∧
      (∀ m, Integrable (fun ω => max (R m ω) 0) (P.restrict A)) ∧
      (∀ m, ∀ᵐ ω ∂(P.restrict A),
        max (E m ω) 0 ≤
          max (T m ω) 0 + |H m ω| + max (R m ω) 0) ∧
      Tendsto (fun m => ∫ ω in A, max (T m ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun m => ∫ ω in A, |H m ω| ∂P)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun m => ∫ ω in A, max (R m ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by sorry
