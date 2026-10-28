-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_chunk06_checked
-- name    : D1Bound5.PairLightClosurePrepared30.chunk06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:54.33402+00:00
-- url     : https://prove2.me/theorems/953624f6-c7b8-4b46-9b06-82bf6c06d470
-- title:
--   Indexed mutation-closure certificate for prepared pair 30
-- statement:
--   For prepared pair 30, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure30Chunk06.lean, lines 8-12, SHA-256 f53d8880c278a95d901810c3a29c0e521cde6b9c02f1fd0e9bd16ec9b1f9748e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared30.chunk06_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 384) (destinations.drop 384) = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
