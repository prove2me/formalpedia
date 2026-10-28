-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk02_checked
-- name    : D1Bound5.PairLightClosurePrepared6.chunk02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:33.257534+00:00
-- url     : https://prove2.me/theorems/7fc1185e-1d0b-4322-b66c-79ab512f24bd
-- title:
--   Indexed mutation-closure certificate for prepared pair 6
-- statement:
--   For prepared pair 6, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure6Chunk02.lean, lines 8-12, SHA-256 bda7f2463ecdf1ae8bed14d312fc2ed252f2d88446ed9092d4a5021f2945c8c0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6_Definitions

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared6.chunk02_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 128) (destinations.drop 128) = true := by sorry

end D1Bound5.PairLightClosurePrepared6
end
