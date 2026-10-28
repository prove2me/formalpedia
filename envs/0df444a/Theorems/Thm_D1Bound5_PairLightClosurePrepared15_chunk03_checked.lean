-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared15_chunk03_checked
-- name    : D1Bound5.PairLightClosurePrepared15.chunk03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:10.351023+00:00
-- url     : https://prove2.me/theorems/608c64ce-5f1c-4b72-bdf0-47c9a88b1a94
-- title:
--   Indexed mutation-closure certificate for prepared pair 15
-- statement:
--   For prepared pair 15, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure15Chunk03.lean, lines 8-12, SHA-256 478a3a79c62051ac585e5da49f5f0a41def4128823795b4bb22766f63514a575. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared15.chunk03_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 192) (destinations.drop 192) = true := by sorry

end D1Bound5.PairLightClosurePrepared15
end
