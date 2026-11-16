-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_integrated_nat_pgf_quadratic_upper_20261115
-- name    : AvramDividend.Classical.avram_a25_integrated_nat_pgf_quadratic_upper_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:13:16.499464+00:00
-- url     : https://prove2.me/theorems/569d5117-da6f-4a18-9831-bfb2b0a4fe18
-- title:
--   Integrate second-order factorial Taylor bound for a natural-valued count probability-generating function
-- statement:
--   For any natural-valued random count with integrable PGF power and quadratic factorial Taylor polynomial and z∈[0,1], its expected PGF is bounded above by the expected second-order factorial Taylor polynomial. The pointwise bound is theorem avram_a25_nat_pgf_quadratic_factorial_upper_20261115. This is a direct Bochner integral monotonicity step, isolating the analytic PGF inequality from the actual Lévy physical negative-Borel source moments.
-- source:
--   Proved reusable Mathlib integral_mono, new PGF second-order pointwise theorem 512439d3.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a25_integrated_nat_pgf_quadratic_upper_20261115
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hZ : Integrable (fun ω => z ^ (K ω)) P)
    (hPoly : Integrable (fun ω => (1 : ℝ) - (1 - z) * (K ω : ℝ) +
      (1 - z) ^ 2 * (K ω : ℝ) * ((K ω : ℝ) - 1) / 2) P) :
    (∫ ω, z ^ (K ω) ∂P) ≤
      (∫ ω, (1 : ℝ) - (1 - z) * (K ω : ℝ) +
        (1 - z) ^ 2 * (K ω : ℝ) * ((K ω : ℝ) - 1) / 2 ∂P) := by sorry
