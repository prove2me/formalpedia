-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk15_checked
-- name    : D1Bound5.PairLightClosurePrepared8.chunk15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:04.014338+00:00
-- url     : https://prove2.me/theorems/d8e709d4-b9e2-4509-85ce-fad79db01010
-- title:
--   Indexed mutation-closure certificate for prepared pair 8
-- statement:
--   For prepared pair 8, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure8Chunk15.lean, lines 8-12, SHA-256 2fd07b7560eadd38ffd8f401269f70a8079422eb210edc777c85caf5813a6b53. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared8.chunk15_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 960) (destinations.drop 960) = true := by sorry

end D1Bound5.PairLightClosurePrepared8
end
