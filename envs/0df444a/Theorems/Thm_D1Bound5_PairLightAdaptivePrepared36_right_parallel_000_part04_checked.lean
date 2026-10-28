-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.right_parallel_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:57.83641+00:00
-- url     : https://prove2.me/theorems/a2c90e23-6187-457d-99a0-3d5b7269f3ee
-- title:
--   Selected-floor prefix certificate for prepared pair 36, right list, part 4
-- statement:
--   For prepared pair 36, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 48 through 59, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight36_000Part04.lean, lines 10-14, SHA-256 54be75dd27c56884e6bcbd31ca2997d163e45b3c3488aaf10ea9fe5bec28a33e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.right_parallel_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 48) (PairLightPrepared36.rightRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
