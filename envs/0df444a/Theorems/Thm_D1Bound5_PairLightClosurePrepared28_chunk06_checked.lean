-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared28_chunk06_checked
-- name    : D1Bound5.PairLightClosurePrepared28.chunk06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:24.567987+00:00
-- url     : https://prove2.me/theorems/59e3a737-c839-4cb1-b5e7-56b527602b42
-- title:
--   Indexed mutation-closure certificate for prepared pair 28
-- statement:
--   For prepared pair 28, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure28Chunk06.lean, lines 8-12, SHA-256 2632f985b3db8310fd7a3ef19b7960b7e50c76db6cd6ae12d86ad2330f550103. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared28.chunk06_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 384) (destinations.drop 384) = true := by sorry

end D1Bound5.PairLightClosurePrepared28
end
