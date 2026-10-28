-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk10_checked
-- name    : D1Bound5.PairLightClosurePrepared23.chunk10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:12.361553+00:00
-- url     : https://prove2.me/theorems/4ccf8f8b-84a2-44eb-8a2e-90661ae4bfbb
-- title:
--   Indexed mutation-closure certificate for prepared pair 23
-- statement:
--   For prepared pair 23, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure23Chunk10.lean, lines 8-12, SHA-256 324831f0390d1cfa805a5be37fb7095280125c49b0b6c76bd1faf46986677f27. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared23.chunk10_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairLightClosurePrepared23
end
