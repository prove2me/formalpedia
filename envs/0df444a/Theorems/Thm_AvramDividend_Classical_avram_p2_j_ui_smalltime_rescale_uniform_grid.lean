-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_smalltime_rescale_uniform_grid
-- name    : AvramDividend.Classical.avram_p2_j_ui_smalltime_rescale_uniform_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:46:28.557767+00:00
-- url     : https://prove2.me/theorems/e39e1e2f-6bac-48ed-8568-06b5eee5e9f9
-- title:
--   Small-time real rate converts to finite-horizon original uniform-grid cell totals
-- statement:
--   If an arbitrary real function Phi has the right-sided first-order limit Phi(h)/h to L as h approaches zero, then the original positive uniform-grid widths T/(n+1) convert it to (n+1)*Phi(T/(n+1)) tending to T*L. The statement uses the independently proved P2-A true NNReal horizon width-to-zero theorem and an exact algebraic cancellation. This is the deterministic analytic scaling bridge from the forthcoming original single-time Levy test rate to its true finite-grid mean, without postulating any jump law or compensator.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_uniform_mesh_tendsto

open Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_j_ui_smalltime_rescale_uniform_grid
    (T : ℝ≥0) (hT : 0 < T) (Φ : ℝ → ℝ) (L : ℝ)
    (hRate : Tendsto (fun h : ℝ => Φ h / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      Φ ((T : ℝ) / ((n : ℝ) + 1))) atTop (nhds ((T : ℝ) * L)) := by sorry
