-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB56_bounded_linear_cell_memLp_two
-- name    : AvramDividend.Classical.avram_gbB56_bounded_linear_cell_memLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:24:33.462512+00:00
-- url     : https://prove2.me/theorems/15674dd4-7a1f-4d28-bcee-c1ddc99bafcc
-- title:
--   Bounded measurable coefficient times square-integrable real noise is in L2
-- statement:
--   A measurable uniformly bounded real coefficient multiplying a measurable random variable with integrable square is square integrable on the same measure space.
-- source:
--   Root-connected finite-grid square-integrability ingredient for gb53 original Gaussian postpayment martingale cells, 11 November 2026.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gbB56_bounded_linear_cell_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F Z : Ω → ℝ) (K : ℝ)
    (hF : Measurable F) (hZ : Measurable Z)
    (hK : 0 ≤ K) (hFb : ∀ ω, |F ω| ≤ K)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ) :
    MemLp (fun ω => F ω * Z ω) 2 μ := by sorry
