-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk14_checked
-- name    : D1Bound5.PairLightClosurePrepared8.chunk14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:09.213488+00:00
-- url     : https://prove2.me/theorems/2c052a12-109c-4bf4-a619-906832ae9520
-- title:
--   Indexed mutation-closure certificate for prepared pair 8
-- statement:
--   For prepared pair 8, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure8Chunk14.lean, lines 8-12, SHA-256 97934f600e621c1c87f2b64e5593564c410e466805ee70697fa4e359a9db2563. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8_Definitions

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared8.chunk14_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 896) (destinations.drop 896) = true := by sorry

end D1Bound5.PairLightClosurePrepared8
end
