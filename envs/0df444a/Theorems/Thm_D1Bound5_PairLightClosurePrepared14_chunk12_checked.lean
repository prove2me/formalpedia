-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared14_chunk12_checked
-- name    : D1Bound5.PairLightClosurePrepared14.chunk12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:13.423683+00:00
-- url     : https://prove2.me/theorems/009e097e-c443-42cd-82fe-02637350bd08
-- title:
--   Indexed mutation-closure certificate for prepared pair 14
-- statement:
--   For prepared pair 14, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure14Chunk12.lean, lines 8-12, SHA-256 de4a9534a020d4c8f8da6df7fd2309fc61ab88ddc2019b45856f6cc8b3dc9424. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared14.chunk12_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 768) (destinations.drop 768) = true := by sorry

end D1Bound5.PairLightClosurePrepared14
end
