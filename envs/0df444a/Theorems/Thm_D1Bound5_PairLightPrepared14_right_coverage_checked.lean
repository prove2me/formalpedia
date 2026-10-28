-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared14_right_coverage_checked
-- name    : D1Bound5.PairLightPrepared14.right_coverage_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:14:42.045167+00:00
-- url     : https://prove2.me/theorems/fda7f929-8c4b-4274-8927-0fe27b8c1156
-- title:
--   Pair Light Prepared14 — right coverage checked
-- statement:
--   Auxiliary result `PairLightPrepared14.right_coverage_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight14.lean, lines 12-14, SHA-256 af4d7dcbdb7149f2b5ca9273bd6555c129e9aa414d611151d54dd78e6d618e5d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightVertices_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared14.right_coverage_checked :
    decide (rightCached.map Prod.fst = rightVertices) = true := by sorry







end D1Bound5.PairLightPrepared14
end
