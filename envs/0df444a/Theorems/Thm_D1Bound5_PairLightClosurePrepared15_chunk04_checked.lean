-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared15_chunk04_checked
-- name    : D1Bound5.PairLightClosurePrepared15.chunk04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:47.855187+00:00
-- url     : https://prove2.me/theorems/720cb41b-1644-47ca-bcb0-793b93ee8187
-- title:
--   Indexed mutation-closure certificate for prepared pair 15
-- statement:
--   For prepared pair 15, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure15Chunk04.lean, lines 8-12, SHA-256 cda0d3a0f68d5159ecf9d41ed03aaf883bc7fc2ccd7632dfb848652c243f88b7. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared15.chunk04_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 256) (destinations.drop 256) = true := by sorry

end D1Bound5.PairLightClosurePrepared15
end
