-- Prove2me | Theorems.Thm_D1Bound5_pellFieldCoverageBlock05_checked
-- name    : D1Bound5.pellFieldCoverageBlock05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:36:26.168541+00:00
-- url     : https://prove2.me/theorems/b775a4e1-d061-438e-a8a7-24314fa5c63e
-- title:
--   Pell Field Coverage Block05 checked
-- statement:
--   Exact coverage of original indices 250 through 299.
-- source:
--   D1Bound5/PellFiniteFieldCoverageBlock05.lean, lines 7-10, SHA-256 add3d70443bc390f8ddb7ab4f051007585ca9f8da667e4a1ff0aa19e1c6b4a47. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


theorem _root_.D1Bound5.pellFieldCoverageBlock05_checked :
    ∀ k : Fin 50, PellFieldCoverageLightAt (250+k.val) := by sorry

end D1Bound5
end
