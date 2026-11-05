-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:38:57.588038+00:00
-- url     : https://prove2.me/theorems/4e1b942c-1c5c-4123-806f-ddc9bce39831
-- title:
--   Original BV source residual nonpositive expectation from vanishing L1 mesh error
-- statement:
--   If finite-grid original BV residuals have nonpositive expectation and their L1 distance to an integrable limiting residual tends to zero, the actual residual also has nonpositive expectation. This route needs the genuine P3-D Taylor L1 error estimates but does not require one uniform a.e. pointwise envelope.
-- source:
--   Pinned Mathlib integral_mono_ae, integral_add and ge_of_tendsto, revision 0df444a360eaa60ab8c11dca51a86af692955474; original P3-D quantitative mesh-error lemmas.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.OrderClosed
open MeasureTheory Filter

theorem AvramDividend.Classical.avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : Ω → ℝ) (Rmesh : ℕ → Ω → ℝ)
    (hR : Integrable R P)
    (hMesh : ∀ n, Integrable (Rmesh n) P)
    (hMean : ∀ n, (∫ ω, Rmesh n ω ∂P) ≤ 0)
    (hError : Tendsto (fun n => (∫ ω, |Rmesh n ω - R ω| ∂P))
      atTop (nhds (0 : ℝ))) :
    (∫ ω, R ω ∂P) ≤ 0 := by sorry
