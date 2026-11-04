-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_left_endpoint_limit_of_vanishing_real_mesh_width
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_left_endpoint_limit_of_vanishing_real_mesh_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:45:15.012215+00:00
-- url     : https://prove2.me/theorems/e4d9859a-fecd-4e50-8ab4-ffca016c048c
-- title:
--   Vanishing real mesh widths force left endpoints to follow right endpoint limits
-- statement:
--   Whenever right endpoints converge in NNReal and their real-valued difference from left endpoints tends to zero, the left endpoints converge to the same NNReal limit. Uses only continuity of subtraction and the NNReal closed embedding.

import Mathlib

namespace AvramDividend.Classical
end AvramDividend.Classical

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_left_endpoint_limit_of_vanishing_real_mesh_width
    (a b : ℕ → ℝ≥0) (t : ℝ≥0)
    (hb : Tendsto b atTop (𝓝 t))
    (hgap : Tendsto (fun n => (b n : ℝ) - (a n : ℝ))
      atTop (𝓝 (0 : ℝ))) :
    Tendsto a atTop (𝓝 t) := by sorry
