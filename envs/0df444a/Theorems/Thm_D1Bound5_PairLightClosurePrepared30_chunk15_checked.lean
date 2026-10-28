-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_chunk15_checked
-- name    : D1Bound5.PairLightClosurePrepared30.chunk15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:21.44676+00:00
-- url     : https://prove2.me/theorems/f2685ec8-cc73-442e-b838-e76aa0390763
-- title:
--   Indexed mutation-closure certificate for prepared pair 30
-- statement:
--   For prepared pair 30, the indexed closure certificate succeeds for at most `3` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure30Chunk15.lean, lines 8-12, SHA-256 61c236dbbde4d7cf4f502e7d99c49433ae79e8033e5a5ad6baebe38126c6ed96. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared30.chunk15_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 3
      (witnesses.drop 960) (destinations.drop 960) = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
