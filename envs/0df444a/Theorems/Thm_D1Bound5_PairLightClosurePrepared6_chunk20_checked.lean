-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk20_checked
-- name    : D1Bound5.PairLightClosurePrepared6.chunk20_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:29.189095+00:00
-- url     : https://prove2.me/theorems/833611a0-933f-4286-86e4-2b8fed983f44
-- title:
--   Indexed mutation-closure certificate for prepared pair 6
-- statement:
--   For prepared pair 6, the indexed closure certificate succeeds for at most `38` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure6Chunk20.lean, lines 8-12, SHA-256 e3df3a1dcea488e795c14d27af7455663ced76fd6e5d7f5477011a532408c581. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared6.chunk20_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 38
      (witnesses.drop 1280) (destinations.drop 1280) = true := by sorry

end D1Bound5.PairLightClosurePrepared6
end
