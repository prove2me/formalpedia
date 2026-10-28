-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk11_checked
-- name    : D1Bound5.PairLightClosurePrepared23.chunk11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:44.695787+00:00
-- url     : https://prove2.me/theorems/4f6907fc-f53c-494c-bc96-39108858012e
-- title:
--   Indexed mutation-closure certificate for prepared pair 23
-- statement:
--   For prepared pair 23, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure23Chunk11.lean, lines 8-12, SHA-256 486e08f6f7fe4c305b908a3e2ca786348e3f90040cebbba18b7f132ccc6d156a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared23.chunk11_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 704) (destinations.drop 704) = true := by sorry

end D1Bound5.PairLightClosurePrepared23
end
