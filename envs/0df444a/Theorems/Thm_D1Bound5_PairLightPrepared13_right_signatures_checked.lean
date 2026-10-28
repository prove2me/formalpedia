-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared13_right_signatures_checked
-- name    : D1Bound5.PairLightPrepared13.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:29:49.81217+00:00
-- url     : https://prove2.me/theorems/e94275ba-8883-4eac-b4f2-0a836714df6b
-- title:
--   Pair Light Prepared13 — right signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared13.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight13.lean, lines 13-15, SHA-256 48897ae68be62abb314dacf14565a7188cbb84e7fb04b2acc98fd4524e6e969f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_004

section
namespace D1Bound5.PairLightPrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared13.right_signatures_checked :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared13
end
