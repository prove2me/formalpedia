-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_chunk09_checked
-- name    : D1Bound5.PairLightClosurePrepared30.chunk09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:35.112708+00:00
-- url     : https://prove2.me/theorems/15612358-92f2-4e38-a2ad-b06d91075172
-- title:
--   Indexed mutation-closure certificate for prepared pair 30
-- statement:
--   For prepared pair 30, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure30Chunk09.lean, lines 8-12, SHA-256 2de6b376682dec3355e283dad6f91896532b7deb30b4cc9a793746c8a0187c77. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared30.chunk09_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 576) (destinations.drop 576) = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
