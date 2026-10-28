-- Prove2me | Theorems.Thm_D1Bound5_pellFieldCoverageBlock14_checked
-- name    : D1Bound5.pellFieldCoverageBlock14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:42.820992+00:00
-- url     : https://prove2.me/theorems/84542bdd-4a39-44fb-ae13-bf0f95eca4d1
-- title:
--   Pell Field Coverage Block14 checked
-- statement:
--   Exact coverage of original indices 700 through 749.
-- source:
--   D1Bound5/PellFiniteFieldCoverageBlock14.lean, lines 7-10, SHA-256 8b9298c469500caff163b7cf9734fb1a09a5953abd7e91648496ae2bf187dffd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


theorem _root_.D1Bound5.pellFieldCoverageBlock14_checked :
    ∀ k : Fin 50, PellFieldCoverageLightAt (700+k.val) := by sorry

end D1Bound5
end
