-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_restricted_real_L1_two_limits_unique_ae
-- name    : AvramDividend.Classical.avram_ga_restricted_real_L1_two_limits_unique_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:38:06.440242+00:00
-- url     : https://prove2.me/theorems/58fd39f2-8c23-4aad-9dce-5910c37a040f
-- title:
--   Restricted real L1 convergence has unique almost-sure limit
-- statement:
--   If a sequence of real integrable random variables converges in mean absolute difference to two integrable limits on an event, those two limits agree almost surely on that event. The proof is by the triangle inequality and zero integral of a nonnegative difference.

import Mathlib
open MeasureTheory Filter Topology

theorem AvramDividend.Classical.avram_ga_restricted_real_L1_two_limits_unique_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (N N0 : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hNI : Integrable N (P.restrict A))
    (hN0I : Integrable N0 (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
       atTop (nhds (0 : ℝ)))
    (hL10 : Tendsto (fun m => ∫ ω in A, |N0 ω - M m ω| ∂P)
       atTop (nhds (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), N ω = N0 ω := by sorry
