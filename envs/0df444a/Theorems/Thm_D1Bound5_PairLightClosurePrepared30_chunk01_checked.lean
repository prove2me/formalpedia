-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_chunk01_checked
-- name    : D1Bound5.PairLightClosurePrepared30.chunk01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:37.838758+00:00
-- url     : https://prove2.me/theorems/7e2cd592-b5e4-4aa3-b8b5-27fd8f5499e7
-- title:
--   Indexed mutation-closure certificate for prepared pair 30
-- statement:
--   For prepared pair 30, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure30Chunk01.lean, lines 8-12, SHA-256 44e5c888d9ffffb04dcd1ec7b3a0f0c3bea900187123f6c6a747bb5cc0cc26dd. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared30.chunk01_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 64) (destinations.drop 64) = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
