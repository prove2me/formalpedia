-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared19_right_independent_checked
-- name    : D1Bound5.PairLightPrepared19.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:10:09.176188+00:00
-- url     : https://prove2.me/theorems/05fc6cbb-13ca-42c6-b3cf-e30836b9611a
-- title:
--   Pair Light Prepared19 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared19.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight19.lean, lines 19-39, SHA-256 0978d1e6c75648a1c52cb1d3f2fff4369333a74101f1cde8e5ea9dc5bda948eb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared19.right_independent_checked :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared19
end
