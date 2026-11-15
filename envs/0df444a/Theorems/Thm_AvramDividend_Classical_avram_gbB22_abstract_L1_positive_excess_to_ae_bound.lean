-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB22_abstract_L1_positive_excess_to_ae_bound
-- name    : AvramDividend.Classical.avram_gbB22_abstract_L1_positive_excess_to_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:30:31.371649+00:00
-- url     : https://prove2.me/theorems/15387a24-aa35-4584-9252-f13639d2bda1
-- title:
--   Vanishing integrable positive mesh excess and L1 mesh convergence force an almost-everywhere upper bound
-- statement:
--   If the positive excess of F above mesh approximants M_m and allowance B has vanishing expected value on A, and the meshes converge to N in L1 on A, then F is bounded almost everywhere on A by N+B. This deterministic functional-analytic transfer includes all integrability assumptions.
-- source:
--   Explicit integral_mono_ae and L1 triangle estimate, followed by integral_eq_zero_iff_of_nonneg_ae. Supplies a sound finite-grid excess-to-pathwise-limit transfer for original Gaussian stopped cash.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB22_abstract_L1_positive_excess_to_ae_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (F N B : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hI : IntegrableOn (fun ω => max (F ω - N ω - B ω) 0) A P)
    (hMI : ∀ m, IntegrableOn
      (fun ω => max (F ω - M m ω - B ω) 0) A P)
    (hDI : ∀ m, IntegrableOn (fun ω => |N ω - M m ω|) A P)
    (hEL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hR : Tendsto (fun m =>
      ∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), F ω ≤ N ω + B ω := by sorry
