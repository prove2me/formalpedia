-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk05_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:52.503097+00:00
-- url     : https://prove2.me/theorems/3cd8ef5b-25b0-457e-84c9-0f49c620bd4d
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk05.lean, lines 8-12, SHA-256 a2b8f229ad331f47c7884c659710652b0e44718b2f262ecd878ba26e98a3bf45. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk05_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 320) (destinations.drop 320) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
