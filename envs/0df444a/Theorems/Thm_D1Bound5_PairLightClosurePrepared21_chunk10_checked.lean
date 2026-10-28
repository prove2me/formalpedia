-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk10_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:59.196608+00:00
-- url     : https://prove2.me/theorems/85d1e75f-a146-430b-86ce-df156909cf98
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk10.lean, lines 8-12, SHA-256 98afb57d84de23d94b1bbdc43c0681f8906b928ef19223a3410d50559a8c2dc9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk10_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 640) (destinations.drop 640) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
