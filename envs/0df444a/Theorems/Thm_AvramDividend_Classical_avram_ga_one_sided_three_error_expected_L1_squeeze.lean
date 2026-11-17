-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_three_error_expected_L1_squeeze
-- name    : AvramDividend.Classical.avram_ga_one_sided_three_error_expected_L1_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:04:56.559315+00:00
-- url     : https://prove2.me/theorems/a869707d-3257-4598-b67b-f2f786ed0299
-- title:
--   Expected positive full-cell source vanishes under one-sided Taylor, Hessian and discount L1 budgets
-- statement:
--   For an integrable stopped full-cell error on any event, suppose its positive part is almost surely dominated by positive Taylor remainder plus absolute Hessian raw-centred cross plus positive discounted-cross error. If the expected three dominating nonnegative errors vanish, the expected positive full-cell residual vanishes. Exactly matches the one-sided B71 caplinear finite-grid inequality, instead of an equality-based three-source glue.

import Mathlib
open MeasureTheory Filter Topology

theorem AvramDividend.Classical.avram_ga_one_sided_three_error_expected_L1_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (F T B C : ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) (P.restrict A))
    (hTI : ∀ m, Integrable (fun ω => max (T m ω) 0) (P.restrict A))
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) (P.restrict A))
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) (P.restrict A))
    (hBound : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      max (F m ω) 0 ≤ max (T m ω) 0 + |B m ω| + max (C m ω) 0)
    (hTt : Tendsto (fun m => ∫ ω in A, max (T m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω in A, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω in A, max (C m ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A, max (F m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
