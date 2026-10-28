-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared14_chunk10_checked
-- name    : D1Bound5.PairLightClosurePrepared14.chunk10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:46.318873+00:00
-- url     : https://prove2.me/theorems/4751a7b4-7f8d-42c5-811f-c698e1ff0de7
-- title:
--   Indexed mutation-closure certificate for prepared pair 14
-- statement:
--   For prepared pair 14, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure14Chunk10.lean, lines 8-12, SHA-256 7ed9eb4dda063b99717ac83b9327a43852f5b6d4789c3563a0f600bb0c8043ff. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared14.chunk10_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairLightClosurePrepared14
end
