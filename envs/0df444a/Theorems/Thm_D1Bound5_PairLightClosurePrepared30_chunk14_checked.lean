-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared30_chunk14_checked
-- name    : D1Bound5.PairLightClosurePrepared30.chunk14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:52.335916+00:00
-- url     : https://prove2.me/theorems/2ab81ca5-e460-4056-b476-d31b5891741c
-- title:
--   Indexed mutation-closure certificate for prepared pair 30
-- statement:
--   For prepared pair 30, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure30Chunk14.lean, lines 8-12, SHA-256 e4a08e3b7ed3e60208ae415c499b70308be4ccf6ba9a96a0c78feae7cb9e13c1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared30.chunk14_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 896) (destinations.drop 896) = true := by sorry

end D1Bound5.PairLightClosurePrepared30
end
