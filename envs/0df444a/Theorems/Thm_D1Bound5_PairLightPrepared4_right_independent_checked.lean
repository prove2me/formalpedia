-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared4_right_independent_checked
-- name    : D1Bound5.PairLightPrepared4.right_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:39:28.495588+00:00
-- url     : https://prove2.me/theorems/05b88bd7-b764-404e-8a3c-b6f10f7c680c
-- title:
--   Pair Light Prepared4 — right independent checked
-- statement:
--   Auxiliary result `PairLightPrepared4.right_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightRight4.lean, lines 21-51, SHA-256 af490fafe2140096d1196861c7c81d7b7312ce7cc6bf879f24e18e7238508656. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared4.right_independent_checked :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by sorry



end D1Bound5.PairLightPrepared4
end
