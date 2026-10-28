-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_chunk12_checked
-- name    : D1Bound5.PairLightClosurePrepared30.chunk12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:40.398201+00:00
-- url     : https://prove2.me/theorems/713a40f1-6439-48ef-84c8-a5098cfce70b
-- title:
--   Indexed mutation-closure certificate for prepared pair 30
-- statement:
--   For prepared pair 30, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure30Chunk12.lean, lines 8-12, SHA-256 0d6aed50bef64cddf897a0d0c5467b8ebb86e8ab901e9708923f180024486d01. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared30.chunk12_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 768) (destinations.drop 768) = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
