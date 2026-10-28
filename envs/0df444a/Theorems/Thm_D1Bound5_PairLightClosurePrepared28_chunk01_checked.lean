-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared28_chunk01_checked
-- name    : D1Bound5.PairLightClosurePrepared28.chunk01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:24.174295+00:00
-- url     : https://prove2.me/theorems/c6ef3b4e-4bd3-42ae-9fb7-488fb981c84b
-- title:
--   Indexed mutation-closure certificate for prepared pair 28
-- statement:
--   For prepared pair 28, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure28Chunk01.lean, lines 8-12, SHA-256 01cf719a7daf98f6d51c2557fd85cfa02d1bc183fa47f31dc5c28ade38aeff64. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared28.chunk01_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 64) (destinations.drop 64) = true := by sorry

end D1Bound5.PairLightClosurePrepared28
end
