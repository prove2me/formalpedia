-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk05_checked
-- name    : D1Bound5.PairLightClosurePrepared6.chunk05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:27.376633+00:00
-- url     : https://prove2.me/theorems/e9ef90cb-8003-4b4c-a11c-e66a25ac3961
-- title:
--   Indexed mutation-closure certificate for prepared pair 6
-- statement:
--   For prepared pair 6, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure6Chunk05.lean, lines 8-12, SHA-256 857c8a76bd1493208b7067aef45b6b5e9b2f1cdf36e19411435bea5d2c121ec7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared6.chunk05_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 320) (destinations.drop 320) = true := by sorry

end D1Bound5.PairLightClosurePrepared6
end
