-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk03_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:36.89969+00:00
-- url     : https://prove2.me/theorems/9af1ea1a-3604-45f7-8599-3e750e92039e
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk03.lean, lines 8-12, SHA-256 54b4d5353a33bd19bb58b3129421e3aea2bf6c352b992bfafb040f725a22dd89. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk03_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 192) (destinations.drop 192) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
