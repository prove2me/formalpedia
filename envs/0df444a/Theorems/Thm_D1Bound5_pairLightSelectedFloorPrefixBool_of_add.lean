-- Prove2me | Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add
-- name    : D1Bound5.pairLightSelectedFloorPrefixBool_of_add
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:50.304928+00:00
-- url     : https://prove2.me/theorems/88719507-b2ee-4469-a64e-34390863e4b2
-- title:
--   Selected-floor prefix certificate
-- statement:
--   the selected-floor certificate succeeds for at most `(m+n)` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = tau and ν = nu, and the sieve is `sieve`. Join two checked finite prefixes without re-executing either certificate.
-- source:
--   D1Bound5/PairLightArithmeticPrefixConcat.lean, lines 35-44, SHA-256 2a00628c416022cc78732a0b0067542b89f738f591b1289ce4370ba3279d0d3b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.pairLightSelectedFloorPrefixBool_of_add
    (tau nu : Int) (sieve : List (Nat × Nat)) (m n : Nat)
    (cached : List PairLightCachedVertex) (rows : List (Nat × List Nat))
    (hm : pairLightSelectedFloorPrefixBool tau nu sieve m cached rows = true)
    (hn : pairLightSelectedFloorPrefixBool tau nu sieve n
      (cached.drop m) (rows.drop m) = true) :
    pairLightSelectedFloorPrefixBool tau nu sieve (m+n) cached rows = true := by sorry

end D1Bound5
end
