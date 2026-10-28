-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared28_chunk05_checked
-- name    : D1Bound5.PairLightClosurePrepared28.chunk05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:06.09855+00:00
-- url     : https://prove2.me/theorems/64599081-814c-4cc1-b66b-85ee6d33e437
-- title:
--   Indexed mutation-closure certificate for prepared pair 28
-- statement:
--   For prepared pair 28, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure28Chunk05.lean, lines 8-12, SHA-256 f8ced5f5cad08bb231e8f97488a92b9631c75f7355765920763eb8ed1c8086e3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared28.chunk05_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 320) (destinations.drop 320) = true := by sorry

end D1Bound5.PairLightClosurePrepared28
end
