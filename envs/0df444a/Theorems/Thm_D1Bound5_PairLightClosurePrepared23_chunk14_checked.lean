-- Prove2me | Theorems.Thm_D1Bound5_PairLightClosurePrepared23_chunk14_checked
-- name    : D1Bound5.PairLightClosurePrepared23.chunk14_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:59.216497+00:00
-- url     : https://prove2.me/theorems/5e0e4a44-1d91-475f-8e2b-030143211ce1
-- title:
--   Indexed mutation-closure certificate for prepared pair 23
-- statement:
--   For prepared pair 23, the indexed closure certificate succeeds for at most `64` supplied witness rows. For each row, the two supplied square roots are checked and both signed mutations are verified either by an exact lookup in the complete original vertex list or by a norm strictly exceeding `(10^1100)`. Both signs retain the full original global destination vertex list.
-- source:
--   D1Bound5/SmallPairPureClosure23Chunk14.lean, lines 8-12, SHA-256 2cb322fd098c4d4268466ade4a083a4539f0660f08774257ecb73c36d83db8fb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightClosurePrepared23.chunk14_checked :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 896) (destinations.drop 896) = true := by sorry

end D1Bound5.PairLightClosurePrepared23
end
