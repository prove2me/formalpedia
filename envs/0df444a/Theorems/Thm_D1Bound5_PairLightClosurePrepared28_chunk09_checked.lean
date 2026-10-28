-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared28_chunk09_checked
-- name    : D1Bound5.PairLightClosurePrepared28.chunk09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:02.487206+00:00
-- url     : https://prove2.me/theorems/4440d8f8-f308-49a1-a808-14cf557e0fb7
-- title:
--   Indexed mutation-closure certificate for prepared pair 28
-- statement:
--   For prepared pair 28, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure28Chunk09.lean, lines 8-12, SHA-256 03c6d52ac861c805e76b37733eac4f00eeaa3b8ebfc022addf18670c4d6a89e3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared28.chunk09_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 576) (destinations.drop 576) = true := by sorry

end D1Bound5.PairLightClosurePrepared28
end
