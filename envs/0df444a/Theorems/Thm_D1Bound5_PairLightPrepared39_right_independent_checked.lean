-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared39_right_independent_checked
-- name    : D1Bound5.PairLightPrepared39.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:38:05.738071+00:00
-- url     : https://prove2.me/theorems/c4d66688-e13c-4601-a14c-94ad6cd67db6
-- title:
--   Pair Light Prepared39 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared39.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight39.lean, lines 19-39, SHA-256 3e984b4c3dd027164e52adbf0de13944d176294935d80e01a500d746340b3ba1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared39.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 2 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared39
end
