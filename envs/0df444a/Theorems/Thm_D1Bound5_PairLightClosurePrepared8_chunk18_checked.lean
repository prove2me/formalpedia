-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk18_checked
-- name    : D1Bound5.PairLightClosurePrepared8.chunk18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:05.940334+00:00
-- url     : https://prove2.me/theorems/a308bed3-f0be-4600-97a5-0ec3cc9254e6
-- title:
--   Indexed mutation-closure certificate for prepared pair 8
-- statement:
--   For prepared pair 8, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure8Chunk18.lean, lines 8-12, SHA-256 c9a1b21742db73fae8d8a342fb799c7381b3eceda3eaaba7dda59a890096d8c0. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared8.chunk18_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1152) (destinations.drop 1152) = true := by sorry

end D1Bound5.PairLightClosurePrepared8
end
