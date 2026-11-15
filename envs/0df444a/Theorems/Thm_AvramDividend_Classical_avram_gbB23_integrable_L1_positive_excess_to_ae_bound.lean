-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB23_integrable_L1_positive_excess_to_ae_bound
-- name    : AvramDividend.Classical.avram_gbB23_integrable_L1_positive_excess_to_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:35:21.97932+00:00
-- url     : https://prove2.me/theorems/6036f38c-71d8-42a4-ba43-c111e229ecc1
-- title:
--   Integrable L1 mesh excess yields almost everywhere stopped cash domination
-- statement:
--   An integrable F,N,B and integrable approximating mesh M_m on A admit an almost everywhere upper bound F<=N+B when both the L1 mesh error and positive excess means tend to zero.
-- source:
--   Specialises B22 using integrability closed under subtraction, maximum with zero, and absolute value; avoids repetitive integrability bookkeeping in the original finite-cap stopped cash theorem.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB23_integrable_L1_positive_excess_to_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (F N B : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hFI : IntegrableOn F A P) (hNI : IntegrableOn N A P)
    (hBI : IntegrableOn B A P) (hMI : ∀ m, IntegrableOn (M m) A P)
    (hEL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m => ∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P) atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), F ω ≤ N ω + B ω := by sorry
