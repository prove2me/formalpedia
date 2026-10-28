-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:56.590066+00:00
-- url     : https://prove2.me/theorems/6ee92a84-b9ff-4863-a564-94be8dc9bd19
-- title:
--   Selected-floor prefix certificate for prepared pair 12, left list, part 1
-- statement:
--   For prepared pair 12, left list, part 1, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 29 through 59; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft12_000Part01.lean, lines 7-11, SHA-256 7784693cbdeeddf6ebc854d21c5e7bfc83ca97a6afb0a33bfb780f02fa42baab. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 31
      (leftCached000.drop 29) (leftRows000.drop 29) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
