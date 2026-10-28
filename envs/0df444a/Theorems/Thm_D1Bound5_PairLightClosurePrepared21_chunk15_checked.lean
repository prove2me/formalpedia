-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk15_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:42.979521+00:00
-- url     : https://prove2.me/theorems/4f0c361d-3d11-4de2-a039-99fd494e0b23
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk15.lean, lines 8-12, SHA-256 6528d885401675ba10cb25343875ce0bafa2a40bae8642217a3cc9f2a0adb236. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk15_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 960) (destinations.drop 960) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
