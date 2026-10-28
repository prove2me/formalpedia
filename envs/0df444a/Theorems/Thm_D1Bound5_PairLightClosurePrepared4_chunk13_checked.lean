-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared4_chunk13_checked
-- name    : D1Bound5.PairLightClosurePrepared4.chunk13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:51.550408+00:00
-- url     : https://prove2.me/theorems/c150c69b-943f-4afa-ad6e-a2f2e4d87afe
-- title:
--   Indexed mutation-closure certificate for prepared pair 4
-- statement:
--   For prepared pair 4, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure4Chunk13.lean, lines 8-12, SHA-256 ef18697ee78455d3a6f903b8d5b12c1c8c3e6fc9cfa5155439cd187ed4274b2f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared4.chunk13_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 832) (destinations.drop 832) = true := by sorry

end D1Bound5.PairLightClosurePrepared4
end
