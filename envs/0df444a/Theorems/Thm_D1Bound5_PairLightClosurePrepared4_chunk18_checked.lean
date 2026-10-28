-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared4_chunk18_checked
-- name    : D1Bound5.PairLightClosurePrepared4.chunk18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:19.353554+00:00
-- url     : https://prove2.me/theorems/c8086f81-cbcc-4a86-831f-ac388dcb3cab
-- title:
--   Indexed mutation-closure certificate for prepared pair 4
-- statement:
--   For prepared pair 4, the indexed closure certificate succeeds for at most `43` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure4Chunk18.lean, lines 8-12, SHA-256 932572180cbe085f6d59c03636ca64fc676d4ec192188d1133d8004c5291e6c3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared4.chunk18_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 43
      (witnesses.drop 1152) (destinations.drop 1152) = true := by sorry

end D1Bound5.PairLightClosurePrepared4
end
