-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_prefix_001_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_prefix_001_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:44.404317+00:00
-- url     : https://prove2.me/theorems/11d22fb8-29df-4b11-9ac6-0d7198102f63
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list
-- statement:
--   For prepared pair 21, left list, the selected-floor certificate succeeds for at most `102` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft21_001.lean, lines 17-70, SHA-256 1abc2fec1acc5890c9383ad9aee037fbe6ea5b10fe4823da7608776c181368c3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 102
      leftCached001 leftRows001 = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
