-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_checked
-- name    : D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:47:30.026992+00:00
-- url     : https://prove2.me/theorems/194b7a3f-d130-4918-abe6-09a65c7c7560
-- title:
--   Selected-floor prefix certificate for prepared pair 8, right list
-- statement:
--   For prepared pair 8, right list, the selected-floor certificate succeeds for at most `149` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared8.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight8_005.lean, lines 16-57, SHA-256 5551fef9e482fcffc6768fcc50ca0a91de7a935ffd61abdfa844e4057cdf81af. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 149
      rightCached005 rightRows005 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared8
end
