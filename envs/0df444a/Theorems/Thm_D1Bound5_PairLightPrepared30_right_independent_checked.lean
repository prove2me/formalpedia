-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared30_right_independent_checked
-- name    : D1Bound5.PairLightPrepared30.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:20:59.166715+00:00
-- url     : https://prove2.me/theorems/03e48929-05be-4383-aea8-a29f00123cad
-- title:
--   Pair Light Prepared30 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared30.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight30.lean, lines 19-39, SHA-256 83409733b0d34678b133aeb4d1f8937ec990699a0f041073c7bacd00cfff13da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared30.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared30
end
