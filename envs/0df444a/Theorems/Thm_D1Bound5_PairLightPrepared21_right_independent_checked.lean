-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared21_right_independent_checked
-- name    : D1Bound5.PairLightPrepared21.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:27:55.187659+00:00
-- url     : https://prove2.me/theorems/10c64a3e-8100-4172-b270-d4c5107c3055
-- title:
--   Pair Light Prepared21 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared21.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight21.lean, lines 20-45, SHA-256 a895485463aa85af719f17c007bcede4368f4c2ffa421fb2fdfb0cafffe04033. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared21.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared21
end
