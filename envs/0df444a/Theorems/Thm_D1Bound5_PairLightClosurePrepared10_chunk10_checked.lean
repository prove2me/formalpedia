-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared10_chunk10_checked
-- name    : D1Bound5.PairLightClosurePrepared10.chunk10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:54.927291+00:00
-- url     : https://prove2.me/theorems/8c7a9f28-c55a-48c0-bbe1-6c3dead2e4a8
-- title:
--   Indexed mutation-closure certificate for prepared pair 10
-- statement:
--   For prepared pair 10, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure10Chunk10.lean, lines 8-12, SHA-256 bcf20eebb746856fbf9c6792d6e84921447ce06b93dd2ea0eb5bf244d4660349. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10_Definitions

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared10.chunk10_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairLightClosurePrepared10
end
