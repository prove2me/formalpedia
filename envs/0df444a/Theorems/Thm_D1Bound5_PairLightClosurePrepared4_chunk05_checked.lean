-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared4_chunk05_checked
-- name    : D1Bound5.PairLightClosurePrepared4.chunk05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:49.267565+00:00
-- url     : https://prove2.me/theorems/4d2a60eb-69e0-4553-8fbf-f74bc07e975a
-- title:
--   Indexed mutation-closure certificate for prepared pair 4
-- statement:
--   For prepared pair 4, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure4Chunk05.lean, lines 8-12, SHA-256 412f507032bdf479e4aff16ee76d04dc8972ae51b9e38d087ec126f50ac30ff9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared4.chunk05_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 320) (destinations.drop 320) = true := by sorry

end D1Bound5.PairLightClosurePrepared4
end
