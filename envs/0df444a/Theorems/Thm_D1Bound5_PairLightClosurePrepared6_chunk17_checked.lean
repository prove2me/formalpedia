-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared6_chunk17_checked
-- name    : D1Bound5.PairLightClosurePrepared6.chunk17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:30.889697+00:00
-- url     : https://prove2.me/theorems/10c84c77-ab9f-4d7e-a8cf-d67a7c485291
-- title:
--   Indexed mutation-closure certificate for prepared pair 6
-- statement:
--   For prepared pair 6, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure6Chunk17.lean, lines 8-12, SHA-256 2098d640a77a1c5a8f0e2683a325521e567ccc44ff58cbb78ded95303c584d87. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6_Definitions

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared6.chunk17_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1088) (destinations.drop 1088) = true := by sorry

end D1Bound5.PairLightClosurePrepared6
end
