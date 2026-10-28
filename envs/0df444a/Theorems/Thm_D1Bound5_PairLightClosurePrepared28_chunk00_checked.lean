-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared28_chunk00_checked
-- name    : D1Bound5.PairLightClosurePrepared28.chunk00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:31.566305+00:00
-- url     : https://prove2.me/theorems/24bf892b-a94a-4928-9e4b-325c5ed6acbb
-- title:
--   Indexed mutation-closure certificate for prepared pair 28
-- statement:
--   For prepared pair 28, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure28Chunk00.lean, lines 8-12, SHA-256 b594e355804bc9ee67386e1a2f20967cf0000bc964e80a9f02fce13b5ac6411b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28_Definitions

section
namespace D1Bound5.PairLightClosurePrepared28
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared28.chunk00_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 0) (destinations.drop 0) = true := by sorry

end D1Bound5.PairLightClosurePrepared28
end
