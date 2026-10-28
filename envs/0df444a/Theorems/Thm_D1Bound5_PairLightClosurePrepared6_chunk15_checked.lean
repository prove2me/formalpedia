-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk15_checked
-- name    : D1Bound5.PairLightClosurePrepared6.chunk15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:36.078684+00:00
-- url     : https://prove2.me/theorems/f360aed2-6bdf-4555-bdae-1594332ff5e5
-- title:
--   Indexed mutation-closure certificate for prepared pair 6
-- statement:
--   For prepared pair 6, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure6Chunk15.lean, lines 8-12, SHA-256 4e7fad49623964e8701e034a4177327ea862e500b16a8706008aef88a19ab38d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared6.chunk15_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 960) (destinations.drop 960) = true := by sorry

end D1Bound5.PairLightClosurePrepared6
end
