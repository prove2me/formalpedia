-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:54.481217+00:00
-- url     : https://prove2.me/theorems/07e2fadd-2e25-4d14-a3c4-23e45e850023
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list
-- statement:
--   For prepared pair 21, left list, the selected-floor certificate succeeds for at most `82` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft21_000.lean, lines 15-56, SHA-256 bce7a18eaf9999917340215721d588e7e1b4ab32a34c4004bd11939f60be9832. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 82
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
