-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared23_right_signatures_checked
-- name    : D1Bound5.PairLightPrepared23.right_signatures_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:24.332753+00:00
-- url     : https://prove2.me/theorems/55026702-a3f8-4bdb-bd14-79a09a45e0d6
-- title:
--   Pair Light Prepared23 — right signatures checked
-- statement:
--   Auxiliary result `PairLightPrepared23.right_signatures_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight23.lean, lines 15-17, SHA-256 ec4a7513eb2b3458464c0ee5fb0a2d8321b8f81cec7408f225045551b39add4d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared23.right_signatures_checked :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by sorry





end D1Bound5.PairLightPrepared23
end
