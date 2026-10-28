-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk06_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:03.910934+00:00
-- url     : https://prove2.me/theorems/e4796611-89ab-403f-8bbe-ed0e7a81ca6e
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk06.lean, lines 8-12, SHA-256 8a59a41108dfa5befece1b9607abe36dc073b23962358fc7ad88e6d56023fc57. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk06_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 384) (destinations.drop 384) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
