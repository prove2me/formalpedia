-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared15_chunk02_checked
-- name    : D1Bound5.PairLightClosurePrepared15.chunk02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:58.805711+00:00
-- url     : https://prove2.me/theorems/a3e3b17c-1ce3-41f6-b218-8f825b47e6b1
-- title:
--   Indexed mutation-closure certificate for prepared pair 15
-- statement:
--   For prepared pair 15, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure15Chunk02.lean, lines 8-12, SHA-256 292c42a3e15e3a583877ee399b8d44a23d76df7161c3377fa3c3c043c76079ce. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared15.chunk02_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 128) (destinations.drop 128) = true := by sorry

end D1Bound5.PairLightClosurePrepared15
end
