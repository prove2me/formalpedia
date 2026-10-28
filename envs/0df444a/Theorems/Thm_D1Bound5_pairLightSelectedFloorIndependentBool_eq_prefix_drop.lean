-- Prove2me | Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_eq_prefix_drop
-- name    : D1Bound5.pairLightSelectedFloorIndependentBool_eq_prefix_drop
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:48.454297+00:00
-- url     : https://prove2.me/theorems/6400df62-f6c7-41e5-bf69-1d66f4968683
-- title:
--   Pair Light Selected Floor Independent Bool eq prefix drop
-- statement:
--   Exact factorization for all inputs, including malformed witness lists. The first factor checks each early head against its full tail.
-- source:
--   D1Bound5/PairLightArithmeticChunkProofs.lean, lines 6-31, SHA-256 658b9d78aa5789e1a26cdcfc58f5960c552bb3ae7fdeda34961f362a081828a4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.pairLightSelectedFloorIndependentBool_eq_prefix_drop
    (tau nu : Int) (sieve : List (Nat × Nat)) (n : Nat)
    (cached : List PairLightCachedVertex) (rows : List (Nat × List Nat)) :
    pairLightSelectedFloorIndependentBool tau nu sieve cached rows =
      (pairLightSelectedFloorPrefixBool tau nu sieve n cached rows &&
        pairLightSelectedFloorIndependentBool tau nu sieve (cached.drop n) (rows.drop n)) := by sorry





end D1Bound5
end
