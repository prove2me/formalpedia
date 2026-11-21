-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_budget_integrable_L1_joint_ito_transfer_signed
-- name    : AvramDividend.Classical.avram_ga_original_budget_integrable_L1_joint_ito_transfer_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:50:03.277639+00:00
-- url     : https://prove2.me/theorems/26f92458-c0ec-46c3-b1cc-4ab7be51c9e8
-- title:
--   Corrected genuine finitecap stopped Ito L1 bridge with signed physical Hessian integrability
-- statement:
--   The original stopped Ito upper bound, global integrability of the Gaussian witness, restricted absolute L1 mesh convergence and a future-masked signed Hessian cross that is itself integrable with absolute L1 norm vanishing imply vanishing expected positive physical-grid reward residual. This version makes signed-measurability of the fullcell cross explicit; mere measurability of its absolute value would be insufficient.
-- source:
--   Corrected source-faithful L1 bridge: directly imports already Proved 7c28d0e2 transfer; the signed fullcell integrability is guaranteed by already Proved 1c5034a4 and absolute L1 limit 7e470c61. Avoids unsound inference of Integrable B from Integrable |B|.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_transfer_stopped_pathwise_L1_positive_source
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_budget_integrable_L1_joint_ito_transfer_signed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (F N Occ : Ω → ℝ) (M B : ℕ → Ω → ℝ) (x Γ c : ℝ)
    (hFI : Integrable F P) (hMI : ∀ m, Integrable (M m) P)
    (hOI : Integrable Occ (P.restrict A))
    (hNI : Integrable N P)
    (hBI : ∀ m, Integrable (B m) P)
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
