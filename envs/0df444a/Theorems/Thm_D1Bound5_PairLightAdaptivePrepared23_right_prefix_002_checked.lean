-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_prefix_002_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_prefix_002_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:05.348228+00:00
-- url     : https://prove2.me/theorems/eb123f7d-dd93-47d7-b028-064309bbe8ce
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list
-- statement:
--   For prepared pair 23, right list, the selected-floor certificate succeeds for at most `266` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight23_002.lean, lines 31-168, SHA-256 7429fd36bf86584bb79adfcff8422793fe093e2bc5f8f75e07b40dd66664f23a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 266
      rightCached002 rightRows002 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
