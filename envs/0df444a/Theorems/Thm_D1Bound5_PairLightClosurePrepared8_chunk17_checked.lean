-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk17_checked
-- name    : D1Bound5.PairLightClosurePrepared8.chunk17_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:04.436285+00:00
-- url     : https://prove2.me/theorems/54b0a37d-2770-45d0-a0fe-5cbd4541fb68
-- title:
--   Indexed mutation-closure certificate for prepared pair 8
-- statement:
--   For prepared pair 8, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure8Chunk17.lean, lines 8-12, SHA-256 171966f9463ae5392baaf74617171d47ed3321beec2871a3e327b9358a425b57. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared8.chunk17_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1088) (destinations.drop 1088) = true := by sorry

end D1Bound5.PairLightClosurePrepared8
end
