-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_physical_L2_convergence_to_Lp_limit
-- name    : AvramDividend.Classical.avram_ubv_gaussian15_physical_L2_convergence_to_Lp_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:43:28.909187+00:00
-- url     : https://prove2.me/theorems/98aed781-5df9-4be7-b212-8d5448b44862
-- title:
--   Physical Gaussian L2 convergence yields canonical Lp convergence for conditional martingale projection
-- statement:
--   A sequence of actual square-integrable original-space Gaussian random variables converging to an actual square-integrable physical terminal in expected-square L2 distance induces convergence of their canonical Lp classes to the terminal class. Exact equality of the two distances follows from the a.e. representative identities. This connects the physical terminal construction to the Lp conditional-expectation projection.
-- source:
--   Already Proved Gaussian14 centred L2 completeness proof uses MemLp.coeFn_toLp and Lp.tendsto_Lp_iff_tendsto_eLpNorm'.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian15_physical_L2_convergence_to_Lp_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (Q : ℕ → Ω → ℝ) (L : Ω → ℝ)
    (hQ : ∀ n, MemLp (Q n) 2 P) (hL : MemLp L 2 P)
    (hConv : Tendsto (fun n => eLpNorm (Q n - L) 2 P)
      atTop (𝓝 0)) :
    Tendsto (fun n => (hQ n).toLp (Q n))
      atTop (𝓝 (hL.toLp L)) := by sorry
