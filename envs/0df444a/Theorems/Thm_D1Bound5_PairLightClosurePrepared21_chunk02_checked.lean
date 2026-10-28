-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared21_chunk02_checked
-- name    : D1Bound5.PairLightClosurePrepared21.chunk02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:39.392139+00:00
-- url     : https://prove2.me/theorems/f5f4fdbe-3b6d-4b4c-9b55-bb47653dfe0c
-- title:
--   Indexed mutation-closure certificate for prepared pair 21
-- statement:
--   For prepared pair 21, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure21Chunk02.lean, lines 8-12, SHA-256 0aa1da92adb871d2a3828b83f6c78b0db0ffe6dfc9bf93703823647d306fa2c8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared21.chunk02_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 128) (destinations.drop 128) = true := by sorry

end D1Bound5.PairLightClosurePrepared21
end
