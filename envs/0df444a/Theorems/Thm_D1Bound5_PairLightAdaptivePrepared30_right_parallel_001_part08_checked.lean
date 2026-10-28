-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_001_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:36.076975+00:00
-- url     : https://prove2.me/theorems/02904844-6b76-4144-8474-eb8d57aa885b
-- title:
--   Selected-floor prefix certificate for prepared pair 30, right list, part 8
-- statement:
--   For prepared pair 30, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`. Original heads 188 through 199, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight30_001Part08.lean, lines 10-14, SHA-256 dfb503363c2a33d7a51e6f36786524a52c03022184e7b015ee859e64efd1575b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 188) (PairLightPrepared30.rightRows.drop 188) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
