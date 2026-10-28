-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_prefix_000_checked
-- name    : D1Bound5.PairLightAdaptivePrepared30.left_prefix_000_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:46:13.676308+00:00
-- url     : https://prove2.me/theorems/d87a9a6a-9a90-4a10-8b2d-e026f05c17ae
-- title:
--   Selected-floor prefix certificate for prepared pair 30, left list
-- statement:
--   For prepared pair 30, left list, the selected-floor certificate succeeds for at most `91` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared30.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft30_000.lean, lines 16-63, SHA-256 599802a9047f9467f73366a5c707125d2de0e05ff06f9a1ac8f53193687a198b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared30.left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 91
      leftCached000 leftRows000 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared30
end
