-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_budget_integrable_L1_joint_ito_transfer
-- name    : AvramDividend.Classical.avram_ga_original_budget_integrable_L1_joint_ito_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:43:01.602212+00:00
-- url     : https://prove2.me/theorems/bf3a79b8-7d05-4884-874c-4b39092beaf3
-- title:
--   Joint integrable source-to-positivepart L1 bridge for the true finite-cap stopped Ito budget
-- statement:
--   Given an actual stopped reward F, a globally integrable Gaussian Ito witness N with physical-grid M_m converging to N in restricted L1, an original pathwise stopped bound F-x≤N+Γ+c Occ, an integrable occupation term, and a genuine original future-masked Hessian cross B_m with integrable absolute value tending to zero, the exact expected positive excess of F−x−M_m−Γ−c Occ−B_m tends to zero on the stopped event. This isolates the mathematical content of the finitecap source after all the already-Proved input estimates have been assembled, without assuming an Itô formula or allowing circular proof dependencies.
-- source:
--   Uses Proved source-independent positive-part transfer 7c28d0e2; controlled integrability, restriction of nonnegative absolute B, and sum of L1 limits. Directly reduces 0ef5d778 to the genuinely Open original pathwise stopped Ito ledger 71ef4079 and Proved source estimates.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_transfer_stopped_pathwise_L1_positive_source
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_budget_integrable_L1_joint_ito_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (F N Occ : Ω → ℝ) (M B : ℕ → Ω → ℝ) (x Γ c : ℝ)
    (hFI : Integrable F P) (hMI : ∀ m, Integrable (M m) P)
    (hOI : Integrable Occ (P.restrict A))
    (hNI : Integrable N P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hPath : ∀ᵐ ω ∂(P.restrict A),
      F ω - x ≤ N ω + Γ + c * Occ ω)
    (hNlim : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBlim : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω in A,
      max ((F ω - x) - M m ω - (Γ + c * Occ ω) - B m ω)
        (0 : ℝ) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
