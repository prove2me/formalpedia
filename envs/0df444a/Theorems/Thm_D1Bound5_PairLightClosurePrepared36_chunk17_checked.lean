-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared36_chunk17_checked
-- name    : D1Bound5.PairLightClosurePrepared36.chunk17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:08.979022+00:00
-- url     : https://prove2.me/theorems/b625415a-dbaa-4c14-bc06-66f280ba5ef5
-- title:
--   Indexed mutation-closure certificate for prepared pair 36
-- statement:
--   For prepared pair 36, the indexed closure certificate succeeds for at most `35` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure36Chunk17.lean, lines 8-12, SHA-256 958b4de8dfbbdc6ecf5d80a6bdc647b54db57e261add98aaedf92ab6ab1d3362. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36_Definitions

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared36.chunk17_checked :
    pairLightIndexedWitnessesPrefixBool 1 2 a b anchorRoot (10^1100) vertices 35
      (witnesses.drop 1088) (destinations.drop 1088) = true := by sorry

end D1Bound5.PairLightClosurePrepared36
end
