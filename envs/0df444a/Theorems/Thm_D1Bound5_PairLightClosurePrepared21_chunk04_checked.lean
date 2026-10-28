-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk04_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:59.902633+00:00
-- url     : https://prove2.me/theorems/4c4f80ef-7924-4d3b-a5fd-8cd1906dcf5d
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk04.lean, lines 8-12, SHA-256 52724b26343836bb04f1a93d576c8354bb2642b80b46086d739b791759ca8e26. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk04_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 256) (destinations.drop 256) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
