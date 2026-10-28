-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:48.366834+00:00
-- url     : https://prove2.me/theorems/8a36f1cc-db64-44c1-8273-8e67d2f72aa5
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list
-- statement:
--   For prepared pair 6, right list, the selected-floor certificate succeeds for at most `64` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_000.lean, lines 15-50, SHA-256 0a868f1dbdf98b953e04dae1703ded73ac886b786be283cdb25d44fa07484f88. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 64
      rightCached000 rightRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
