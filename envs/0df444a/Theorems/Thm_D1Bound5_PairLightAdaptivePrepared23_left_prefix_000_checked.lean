-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:43:38.28222+00:00
-- url     : https://prove2.me/theorems/066b8130-92f5-4acb-990b-04318d4787fd
-- title:
--   Selected-floor prefix certificate for prepared pair 23, left list
-- statement:
--   For prepared pair 23, left list, the selected-floor certificate succeeds for at most `91` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft23_000.lean, lines 16-63, SHA-256 6178ff9de923f6e7536d09772e604171f49da67b0983ee86e6addda3ab49b433. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared23.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 91
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
