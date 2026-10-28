-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared4_chunk15_checked
-- name    : D1Bound5.PairLightClosurePrepared4.chunk15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:02.625668+00:00
-- url     : https://prove2.me/theorems/8a8d1fca-fb86-44f0-9752-349c94b73270
-- title:
--   Indexed mutation-closure certificate for prepared pair 4
-- statement:
--   For prepared pair 4, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure4Chunk15.lean, lines 8-12, SHA-256 f5904eb09615f5b0b692f8033aba8192a6b23623e67b2f02fdaa9bcded8014db. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared4.chunk15_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 960) (destinations.drop 960) = true := by sorry

end D1Bound5.PairLightClosurePrepared4
end
