-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_chunk13_checked
-- name    : D1Bound5.PairLightClosurePrepared30.chunk13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:53:19.909805+00:00
-- url     : https://prove2.me/theorems/140002a2-94b2-4460-9d67-a6dac2fad549
-- title:
--   Indexed mutation-closure certificate for prepared pair 30
-- statement:
--   For prepared pair 30, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure30Chunk13.lean, lines 8-12, SHA-256 96ac7e26ec364db6d0d6bef3da0828124e6be391aaae30cd07fd4d27cb19c816. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared30.chunk13_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 832) (destinations.drop 832) = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
