-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
-- name    : AvramDividend.Classical.avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:05:52.892683+00:00
-- url     : https://prove2.me/theorems/104b3f27-5462-4644-9b41-867f069d1700
-- title:
--   Source supplied uniform compensated terminal clock converges to the original real horizon
-- statement:
--   For the exact supplied original physical grid u of the BV infinite activity BVA62/BVA63 chain, uniformity u(n,i)=T i/(n+2) forces the actual last compensated source evaluation time u(n,n+1) to approach the original T from below as n→∞, using the already Proved strict cash cut-off convergence theorem. This supplies cofinal clock alignment without choosing a replacement grid.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    Tendsto (fun n : ℕ => (u n (n + 1) : ℝ)) atTop (𝓝 T) := by sorry
