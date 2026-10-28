-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk01_checked
-- name    : D1Bound5.PairLightClosurePrepared8.chunk01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:12.707337+00:00
-- url     : https://prove2.me/theorems/155299c8-9db5-4732-9680-0de6a58979b0
-- title:
--   Indexed mutation-closure certificate for prepared pair 8
-- statement:
--   For prepared pair 8, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure8Chunk01.lean, lines 8-12, SHA-256 3a2a10f412a7267a46e8faf7d8c52383757d59a8889d4eed23a7ff5b7d8de526. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared8.chunk01_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 64) (destinations.drop 64) = true := by sorry

end D1Bound5.PairLightClosurePrepared8
end
