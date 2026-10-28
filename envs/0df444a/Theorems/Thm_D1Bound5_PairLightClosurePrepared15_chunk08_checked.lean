-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared15_chunk08_checked
-- name    : D1Bound5.PairLightClosurePrepared15.chunk08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:13.498536+00:00
-- url     : https://prove2.me/theorems/ae1a07ca-aab2-4803-8d1b-52921c5d566c
-- title:
--   Indexed mutation-closure certificate for prepared pair 15
-- statement:
--   For prepared pair 15, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure15Chunk08.lean, lines 8-12, SHA-256 417fa92476489c36f13866c1c68c40a3ede631b0884480894491671ecab0cc07. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared15.chunk08_checked :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) = true := by sorry

end D1Bound5.PairLightClosurePrepared15
end
