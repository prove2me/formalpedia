-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared28_right_independent_checked
-- name    : D1Bound5.PairLightPrepared28.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:07:59.739831+00:00
-- url     : https://prove2.me/theorems/e56dfe97-5164-4d1b-9665-aba6d68dcea5
-- title:
--   Pair Light Prepared28 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared28.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight28.lean, lines 20-45, SHA-256 6a38a1adb84ab2ced773905cf6710450f36f8f28f9a8947155a53f5bceceb4d8. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared28.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared28
end
