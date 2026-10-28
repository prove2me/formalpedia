-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk16_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk16_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:42.102348+00:00
-- url     : https://prove2.me/theorems/f1b860ec-74be-4c40-be2f-cea9883757c1
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `25` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk16.lean, lines 8-12, SHA-256 01ac9e555e11df4b6a0cf67538c80bba29b2bf257539e6b74024784ccd410f48. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk16_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 25
      (witnesses.drop 1024) (destinations.drop 1024) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
