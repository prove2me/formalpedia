-- Prove2me | Theorems.Thm_D1Bound5_pellFieldCoverageBlock03_checked
-- name    : D1Bound5.pellFieldCoverageBlock03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:42.17673+00:00
-- url     : https://prove2.me/theorems/78e8299e-3167-471f-bc21-f07cd81d38e7
-- title:
--   Pell Field Coverage Block03 checked
-- statement:
--   Exact coverage of original indices 150 through 199.
-- source:
--   D1Bound5/PellFiniteFieldCoverageBlock03.lean, lines 7-10, SHA-256 7d7ebdfcd29493290afbb42506ec051629a471cfa6238d6c796a9a7ce47316d2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000


theorem _root_.D1Bound5.pellFieldCoverageBlock03_checked :
    ∀ k : Fin 50, PellFieldCoverageLightAt (150+k.val) := by sorry

end D1Bound5
end
