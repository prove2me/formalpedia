-- Prove2me | Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop
-- name    : D1Bound5.pairLightSelectedFloorIndependentBool_of_prefix_drop
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:18.286019+00:00
-- url     : https://prove2.me/theorems/f00bb258-a340-40ed-8a33-cfa80674c27d
-- title:
--   Pair Light Selected Floor Independent Bool of prefix drop
-- statement:
--   Assemble already checked proof constants without rerunning their arithmetic.
-- source:
--   D1Bound5/PairLightArithmeticChunkProofs.lean, lines 33-42, SHA-256 658b9d78aa5789e1a26cdcfc58f5960c552bb3ae7fdeda34961f362a081828a4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.pairLightSelectedFloorIndependentBool_of_prefix_drop
    (tau nu : Int) (sieve : List (Nat × Nat)) (n : Nat)
    (cached : List PairLightCachedVertex) (rows : List (Nat × List Nat))
    (hprefix : pairLightSelectedFloorPrefixBool tau nu sieve n cached rows = true)
    (htail : pairLightSelectedFloorIndependentBool tau nu sieve
      (cached.drop n) (rows.drop n) = true) :
    pairLightSelectedFloorIndependentBool tau nu sieve cached rows = true := by sorry



end D1Bound5
end
