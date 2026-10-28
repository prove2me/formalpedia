-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk19_checked
-- name    : D1Bound5.PairLightClosurePrepared6.chunk19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:21.57956+00:00
-- url     : https://prove2.me/theorems/42207a1b-9e46-456b-96b6-57276892bd10
-- title:
--   Indexed mutation-closure certificate for prepared pair 6
-- statement:
--   For prepared pair 6, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure6Chunk19.lean, lines 8-12, SHA-256 c23b5b61c6ce14dd8b681de7d4e10b4097f5c2280c24dbc8f7d8fec14c1053ab. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared6.chunk19_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1216) (destinations.drop 1216) = true := by sorry

end D1Bound5.PairLightClosurePrepared6
end
