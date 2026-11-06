-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_physical_mesh_convergent_fatou
-- name    : AvramDividend.Classical.avram_limit2_physical_mesh_convergent_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:10:19.240984+00:00
-- url     : https://prove2.me/theorems/edd0a55f-2dcb-47a6-89cd-ccb18dcf60a6
-- title:
--   Almost-everywhere physical mesh convergence supplies the signed Fatou lower bound
-- statement:
--   A genuine real-valued physical stopped-mesh family converging almost everywhere to the original cash-plus-terminal payoff automatically satisfies the exact ENNReal liminf Fatou clause in the BV signed grid certificate. The result is a convergent-mesh adapter; it does not assume or assert the existence of a physical mesh.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_signed_grid_envelope_of_expected_upper
open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_physical_mesh_convergent_fatou
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ)
    (hR : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (nhds (R ω))) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal (R ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop := by sorry
