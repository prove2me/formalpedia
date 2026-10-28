-- Prove2me | Theorems.Thm_D1Bound5_pellFieldCoverageBlock19_checked
-- name    : D1Bound5.pellFieldCoverageBlock19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:36:32.099227+00:00
-- url     : https://prove2.me/theorems/2d502c42-8271-4503-83ae-1135f2f41880
-- title:
--   Pell Field Coverage Block19 checked
-- statement:
--   Exact coverage of original indices 950 through 999.
-- source:
--   D1Bound5/PellFiniteFieldCoverageBlock19.lean, lines 7-10, SHA-256 eb2ca019fe67c71b047e30db73eb1d1bcc7552a50bb9ceee0f9fdf8aadc35bb1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


theorem _root_.D1Bound5.pellFieldCoverageBlock19_checked :
    ∀ k : Fin 50, PellFieldCoverageLightAt (950+k.val) := by sorry

end D1Bound5
end
