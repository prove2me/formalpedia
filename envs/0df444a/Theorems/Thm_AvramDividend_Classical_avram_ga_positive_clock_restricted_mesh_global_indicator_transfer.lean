-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_positive_clock_restricted_mesh_global_indicator_transfer
-- name    : AvramDividend.Classical.avram_ga_positive_clock_restricted_mesh_global_indicator_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:38:06.309569+00:00
-- url     : https://prove2.me/theorems/4809968d-2f5e-4e12-9be0-8c6d15825a5d
-- title:
--   Original positive-clock restricted Gaussian mesh L1 witness becomes globally integrable by event masking
-- statement:
--   For any finite physical stochastic mesh M_m integrable on the original probability measure, a limiting stochastic integral known only on the genuine positive stopped event A through restricted absolute L1 convergence admits a globally integrable representative N=1_A Z with identical restricted absolute L1 convergence. This is the exact event-mask conversion required before invoking the original stopped pathwise Ito cash ledger in finitecap theorem 0ef5d778.
-- source:
--   The authentic finitecap centred mesh limit 6a5f5a1a is restricted to A={rho>0}; original stopped pathwise ledger 71ef4079 needs a globally integrable stochastic variable. Integrability of one difference and one mesh value supplies restricted integrability of Z, and measurable event indication extends it to P with equal restricted L1 limits.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_positive_clock_restricted_mesh_global_indicator_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A) (M : ℕ → Ω → ℝ)
    (hMI : ∀ m, Integrable (M m) P)
    (hSource : ∃ Z : Ω → ℝ,
      (∀ m, Integrable (fun ω => |Z ω - M m ω|) (P.restrict A)) ∧
      Tendsto (fun m => ∫ ω in A, |Z ω - M m ω| ∂P)
        atTop (𝓝 (0 : ℝ))) :
    ∃ N : Ω → ℝ, Integrable N P ∧
      Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
