-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared14_chunk00_checked
-- name    : D1Bound5.PairLightClosurePrepared14.chunk00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:29.851109+00:00
-- url     : https://prove2.me/theorems/34bf7869-ea3d-4fa7-898b-48527053d755
-- title:
--   Indexed mutation-closure certificate for prepared pair 14
-- statement:
--   For prepared pair 14, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure14Chunk00.lean, lines 8-12, SHA-256 1e28ab9880a0934fb4fece4c0888c3066e6691f5dec078022ad723ecefde8add. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared14.chunk00_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 0) (destinations.drop 0) = true := by sorry

end D1Bound5.PairLightClosurePrepared14
end
