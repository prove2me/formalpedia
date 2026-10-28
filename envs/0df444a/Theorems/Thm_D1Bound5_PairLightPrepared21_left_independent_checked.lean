-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared21_left_independent_checked
-- name    : D1Bound5.PairLightPrepared21.left_independent_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:08:21.984935+00:00
-- url     : https://prove2.me/theorems/71acd1c2-9ee1-4793-8ff8-94d8b4c334d9
-- title:
--   Pair Light Prepared21 — left independent checked
-- statement:
--   Auxiliary result `PairLightPrepared21.left_independent_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightLeft21.lean, lines 20-45, SHA-256 e0ab01ff6020d5c6bb95df8163a882dbf98033a5d334f3a54c0501ed3f66715d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.D1Bound5.PairLightPrepared21.left_independent_checked :
    pairLightSelectedFloorIndependentBool 1 1 sieve leftCached leftRows = true := by sorry



end D1Bound5.PairLightPrepared21
end
