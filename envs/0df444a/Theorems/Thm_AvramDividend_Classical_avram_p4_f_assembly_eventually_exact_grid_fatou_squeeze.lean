-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_eventually_exact_grid_fatou_squeeze
-- name    : AvramDividend.Classical.avram_p4_f_assembly_eventually_exact_grid_fatou_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:39:53.718298+00:00
-- url     : https://prove2.me/theorems/0efbba96-51f6-4fdf-9941-731c8b72a934
-- title:
--   Fatou squeeze for eventual original-jump grid pair counts without mesh monotonicity
-- statement:
--   For nonnegative measurable finite-grid counts F_n on the same original probability space, if each is bounded by the full count K, each path is eventually exactly K, and physical expectations of F_n converge to r, then the physical expected full count equals r. One Fatou bound and the reverse monotonicity of integrals prove equality. This removes the need to incorrectly assume that arbitrary uniform grids form a monotone refinement; it is the precise abstract analytic bridge needed to close the original chronological-pair second moment.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_eventually_exact_grid_fatou_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞) (r : ℝ≥0∞)
    (hFm : ∀ n, Measurable (F n))
    (hBound : ∀ n ω, F n ω ≤ K ω)
    (hEventually : ∀ ω, ∀ᶠ n in atTop, F n ω = K ω)
    (hRate : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 r)) :
    (∫⁻ ω, K ω ∂P) = r := by sorry
