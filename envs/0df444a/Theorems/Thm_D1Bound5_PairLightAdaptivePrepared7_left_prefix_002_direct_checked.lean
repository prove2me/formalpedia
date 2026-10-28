-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:12.387813+00:00
-- url     : https://prove2.me/theorems/c779bd2c-35ec-4333-bef2-2d0c31984098
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list
-- statement:
--   For prepared pair 7, left list, the selected-floor certificate succeeds for at most `164` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft7Prefix002.lean, lines 14-55, SHA-256 76c88c31458cfd35039d53112d5d07f8a09b83147042bd8ae38703436bd052fb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 164
      (PairLightPrepared7.leftCached.drop 268) (PairLightPrepared7.leftRows.drop 268) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared7
end
