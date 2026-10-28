-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared28_chunk16_checked
-- name    : D1Bound5.PairLightClosurePrepared28.chunk16_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:19.152605+00:00
-- url     : https://prove2.me/theorems/3396758f-ba66-47c2-acde-21787d433716
-- title:
--   Indexed mutation-closure certificate for prepared pair 28
-- statement:
--   For prepared pair 28, the indexed closure certificate succeeds for at most `26` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure28Chunk16.lean, lines 8-12, SHA-256 e6edc14b0f4595955131272b944f1456fda96502c628bdc6b7717068d23fe2d8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared28.chunk16_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 26
      (witnesses.drop 1024) (destinations.drop 1024) = true := by sorry

end D1Bound5.PairLightClosurePrepared28
end
