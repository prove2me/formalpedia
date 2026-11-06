-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_jump_coefficient_positive_reserve_sequence_continuity
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_jump_coefficient_positive_reserve_sequence_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:22:02.55538+00:00
-- url     : https://prove2.me/theorems/48ae403e-5f2e-48c7-a207-3d1133fcb5c5
-- title:
--   Original jump value coefficient converges at positive pre- and postjump reserve states
-- statement:
--   For the canonical continuous-on-nonnegative value function and a fixed jump whose pre- and postjump reserves are strictly positive, convergence of original reserve grid states implies convergence of exact physical value jump coefficients.
-- source:
--   ContinuousOn w (Ici 0) gives ContinuousAt at strictly positive reserves. Compose with U_k→u and its translated sequence, then subtract. Project definition import supplies source-exact real/filter symbols after targeted Mathlib import optimization.

import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Set
open scoped Topology

/-- Original negative-jump coefficients converge at positive pre- and postjump reserve states. -/

theorem AvramDividend.Classical.avram_p4_f3_original_negative_jump_coefficient_positive_reserve_sequence_continuity
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (u z : ℝ) (hu : 0 < u) (huz : 0 < u + z)
    (U : ℕ → ℝ) (hU : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun k => w (U k + z) - w (U k)) atTop
      (𝓝 (w (u + z) - w u)) := by sorry
