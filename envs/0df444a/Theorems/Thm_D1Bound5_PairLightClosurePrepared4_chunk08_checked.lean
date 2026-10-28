-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared4_chunk08_checked
-- name    : D1Bound5.PairLightClosurePrepared4.chunk08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:14.176065+00:00
-- url     : https://prove2.me/theorems/d20cfa1f-eb85-4752-be55-aaa102b4bf01
-- title:
--   Indexed mutation-closure certificate for prepared pair 4
-- statement:
--   For prepared pair 4, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure4Chunk08.lean, lines 8-12, SHA-256 9cf5400f17eceeb07dae75967517cec60385ed5349a3cdc45c05187b0ae1c86f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared4.chunk08_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) = true := by sorry

end D1Bound5.PairLightClosurePrepared4
end
