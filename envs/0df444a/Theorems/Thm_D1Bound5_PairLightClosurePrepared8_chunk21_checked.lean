-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared8_chunk21_checked
-- name    : D1Bound5.PairLightClosurePrepared8.chunk21_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:09.010039+00:00
-- url     : https://prove2.me/theorems/c51c2480-1924-49de-988e-6f147376ac66
-- title:
--   Indexed mutation-closure certificate for prepared pair 8
-- statement:
--   For prepared pair 8, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure8Chunk21.lean, lines 8-12, SHA-256 834113b3f8f8aadd1e29eac20a2b5f2d74f2157e2ea0bf9fa1cf2e927ebcbd88. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared8.chunk21_checked :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1344) (destinations.drop 1344) = true := by sorry

end D1Bound5.PairLightClosurePrepared8
end
