-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk08_checked
-- name    : D1Bound5.PairLightClosurePrepared8.chunk08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:08.080989+00:00
-- url     : https://prove2.me/theorems/4665d3ab-aa7a-4ec5-9eb7-8dd59aaaa7a5
-- title:
--   Indexed mutation-closure certificate for prepared pair 8
-- statement:
--   For prepared pair 8, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure8Chunk08.lean, lines 8-12, SHA-256 5c071378fdebf713b31277baaeca8bf62796f4ee7ac9ac4e7795329d3d47c84d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared8.chunk08_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) = true := by sorry

end D1Bound5.PairLightClosurePrepared8
end
