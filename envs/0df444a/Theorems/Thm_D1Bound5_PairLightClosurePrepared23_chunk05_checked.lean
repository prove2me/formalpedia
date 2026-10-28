-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk05_checked
-- name    : D1Bound5.PairLightClosurePrepared23.chunk05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:15.789997+00:00
-- url     : https://prove2.me/theorems/53a9e06b-b90c-4b9c-98c9-68010a078c78
-- title:
--   Indexed mutation-closure certificate for prepared pair 23
-- statement:
--   For prepared pair 23, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure23Chunk05.lean, lines 8-12, SHA-256 0768f83b3c759d8f50e69acf0a92838f435afe3c8cffe83c4a9dac8e414433da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightClosurePrepared23.chunk05_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 320) (destinations.drop 320) = true := by sorry

end D1Bound5.PairLightClosurePrepared23
end
