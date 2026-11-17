-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_eventwise_positive_excess_and_global_L1_imply_ae_upper
-- name    : AvramDividend.Classical.avram_ga_eventwise_positive_excess_and_global_L1_imply_ae_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:21:37.805973+00:00
-- url     : https://prove2.me/theorems/62fee35b-f211-4ca9-99eb-3ce7be0343aa
-- title:
--   Restricted positive excess L1 and global L1 approximation imply almost-sure bound on event
-- statement:
--   For a measurable event A and real random variables K and N, if a sequence M tends to N in global L1 and the mean positive excess (K-M) on A tends to zero, with integrability hypotheses, then K <= N almost surely on A. This is an event-restriction and squeeze consequence of standard L1 inequalities.

import Mathlib
open MeasureTheory Filter Topology

theorem AvramDividend.Classical.avram_ga_eventwise_positive_excess_and_global_L1_imply_ae_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (K N : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hKI : Integrable K (P.restrict A)) (hNI : Integrable N P)
    (hMI : ∀ m, Integrable (M m) P)
    (hRes : Tendsto (fun m => ∫ ω in A, max (K ω - M m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hDiff : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ))) :
    ∀ᵐ ω ∂P, ω ∈ A → K ω ≤ N ω := by sorry
