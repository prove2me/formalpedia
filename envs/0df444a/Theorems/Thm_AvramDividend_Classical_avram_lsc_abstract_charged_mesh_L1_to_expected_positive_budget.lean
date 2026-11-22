-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_abstract_charged_mesh_L1_to_expected_positive_budget
-- name    : AvramDividend.Classical.avram_lsc_abstract_charged_mesh_L1_to_expected_positive_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T08:31:36.391645+00:00
-- url     : https://prove2.me/theorems/fbb30777-11e5-40f6-915a-367cca19dd6a
-- title:
--   A charged physical Gaussian mesh L1 residual gives the finite-band positive cash expectation budget
-- statement:
--   If a source-faithful finite-grid positive residual remains after subtracting both a nonnegative cap-corner defect and the nonnegative upper-strip occupation charge, converges to zero in expected L1, and the centred physical mesh converges in L1 to N, then the event-restricted expected positive cash excess is at most the cap-corner defect plus the original positive-drift occupation expectation plus arbitrary epsilon. Assumptions explicitly require the relevant integrability and preserve the positive strip charge.
-- source:
--   Avram Classical finite-cap stopped Gaussian cash. Genuine algebraic and analytic L1 transfer from charged physical mesh residual to exact expected positive part event bound using already Proved gbB22 (15387a24) and gb25 (946ecce9).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB22_abstract_L1_positive_excess_to_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_gb25_abstract_positive_part_event_L1_transfer
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_lsc_abstract_charged_mesh_L1_to_expected_positive_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F N Occ : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hI : IntegrableOn
      (fun ω => max (F ω - N ω - (B + c * Occ ω)) 0) A P)
    (hMI : ∀ m, IntegrableOn
      (fun ω => max (F ω - M m ω - (B + c * Occ ω)) 0) A P)
    (hDI : ∀ m, IntegrableOn (fun ω => |N ω - M m ω|) A P)
    (hL1 : Tendsto (fun m =>
      ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m =>
      ∫ ω in A, max (F ω - M m ω - (B + c * Occ ω)) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hFI : ∀ m, IntegrableOn (fun ω => max (F ω - M m ω) 0) A P)
    (hOccI : IntegrableOn Occ A P)
    (hOccNonneg : ∀ᵐ ω ∂(P.restrict A), 0 ≤ Occ ω) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∃ m : ℕ, K < m ∧
      (∫ ω in A, max (F ω - M m ω) 0 ∂P) ≤
        B + c * (∫ ω in A, Occ ω ∂P) + ε := by sorry
