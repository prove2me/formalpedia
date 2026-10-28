-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared4_chunk02_checked
-- name    : D1Bound5.PairLightClosurePrepared4.chunk02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:40.8138+00:00
-- url     : https://prove2.me/theorems/eb39cdfa-dacc-493f-84fb-4128343454f9
-- title:
--   Indexed mutation-closure certificate for prepared pair 4
-- statement:
--   For prepared pair 4, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure4Chunk02.lean, lines 8-12, SHA-256 e279e50aea5cf3373fcc55aaedb665dae4078ff6055e6bc1c55b2c2f929f9197. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared4.chunk02_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 128) (destinations.drop 128) = true := by sorry

end D1Bound5.PairLightClosurePrepared4
end
