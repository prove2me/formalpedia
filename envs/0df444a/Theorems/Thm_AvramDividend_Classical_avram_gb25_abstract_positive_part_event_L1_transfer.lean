-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb25_abstract_positive_part_event_L1_transfer
-- name    : AvramDividend.Classical.avram_gb25_abstract_positive_part_event_L1_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:55:07.455258+00:00
-- url     : https://prove2.me/theorems/946ecce9-baa3-4a44-bc98-23f6cbc27142
-- title:
--   Abstract eventwise positive-part transfer from pathwise budget and L1 mesh convergence
-- statement:
--   Pure measure-theoretic transfer: if the physical excess is a.s. dominated by a centred-limit variable plus nonnegative cap-strip budget, and the finite-mesh difference converges in event L1, then its expected positive part obeys the same budget with arbitrarily small error on a cofinal mesh. Contains no dividend strategy, process, Gaussian stochastic calculus or any assumption of cash inequality.
-- source:
--   Analytic event integral bridge needed in the sound gb20+gb21 to gfinite61 route.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb25_abstract_positive_part_event_L1_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F N Occ : Ω → ℝ)
    (M : ℕ → Ω → ℝ) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hFI : ∀ m, IntegrableOn (fun ω => max (F ω - M m ω) 0) A P)
    (hOccI : IntegrableOn Occ A P)
    (hErrI : ∀ m, IntegrableOn (fun ω => |N ω - M m ω|) A P)
    (hOccNonneg : ∀ᵐ ω ∂(P.restrict A), 0 ≤ Occ ω)
    (hBudget : ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ N ω + B + c * Occ ω)
    (hL1 : Tendsto (fun m : ℕ =>
      ∫ ω in A, |N ω - M m ω| ∂P) atTop (𝓝 (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ K : ℕ, ∃ m : ℕ, K < m ∧
      (∫ ω in A, max (F ω - M m ω) 0 ∂P) ≤
        B + c * (∫ ω in A, Occ ω ∂P) + ε := by sorry
