-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:31:20.627963+00:00
-- url     : https://prove2.me/theorems/8711fbc8-e61b-4a63-ab99-aa71a772ab8f
-- title:
--   Dominated centered BV jump mesh residuals stay centered at the almost-everywhere limit
-- statement:
--   For centered, strongly measurable finite-grid original jump residuals with a common integrable envelope and a.e. pathwise convergence, dominated convergence transfers the zero mean to the limiting martingale residual. The genuine P3-B same-original-X compensation and P3-D mesh convergence remain independent requirements.
-- source:
--   Pinned Mathlib dominated convergence and Hausdorff uniqueness of limits at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory Filter

theorem AvramDividend.Classical.avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → Ω → ℝ) (Mfinal B : Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (M n) P)
    (hB : Integrable B P)
    (hBound : ∀ n, ∀ᵐ ω ∂P, |M n ω| ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun n => M n ω) atTop (nhds (Mfinal ω)))
    (hMean : ∀ n, (∫ ω, M n ω ∂P) = 0) :
    (∫ ω, Mfinal ω ∂P) = 0 := by sorry
