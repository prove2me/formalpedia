-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared15_chunk15_checked
-- name    : D1Bound5.PairLightClosurePrepared15.chunk15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:16.367998+00:00
-- url     : https://prove2.me/theorems/a43deaf1-bc20-4cf5-8811-baf0d7ccbc51
-- title:
--   Indexed mutation-closure certificate for prepared pair 15
-- statement:
--   For prepared pair 15, the indexed closure certificate succeeds for at most `3` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure15Chunk15.lean, lines 8-12, SHA-256 d1eeb22f7aa50d7c6f4178e893a7873286cff46e01985532e6959bd8b51c46f5. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared15.chunk15_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 3
      (witnesses.drop 960) (destinations.drop 960) = true := by sorry

end D1Bound5.PairLightClosurePrepared15
end
