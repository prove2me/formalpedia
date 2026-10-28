-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared36_chunk11_checked
-- name    : D1Bound5.PairLightClosurePrepared36.chunk11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:49.189348+00:00
-- url     : https://prove2.me/theorems/e0160b14-2749-4dea-9590-891f9ab16c94
-- title:
--   Indexed mutation-closure certificate for prepared pair 36
-- statement:
--   For prepared pair 36, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure36Chunk11.lean, lines 8-12, SHA-256 a75d542eb4cd0886df607efeb1812026409e90915110ba90ac294f7e2ee39392. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36_Definitions

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared36.chunk11_checked :
    pairLightIndexedWitnessesPrefixBool 1 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 704) (destinations.drop 704) = true := by sorry

end D1Bound5.PairLightClosurePrepared36
end
