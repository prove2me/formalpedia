-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared42_left_checked
-- name    : D1Bound5.PairLightPrepared42.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:53.890219+00:00
-- url     : https://prove2.me/theorems/9689b3d7-7cfc-4690-9dc5-0d77e919a690
-- title:
--   Pair Light Prepared42 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared42.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphData42.lean, lines 3040-3045, SHA-256 1ed8ce699593f8600aa064e65c247cf748c5fb803b6b34d6d288dce915fef4cd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData42_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphData42_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_3_Definitions

section
/- Preserved body from D1Bound5.SmallPairGraphInputs42; original SHA256 e751a5007e71d6837bdcdd3b8c93aacd9a20b359f3364e1165d9ae650d464a20. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared42



end PairGraphPrepared42
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic42; original SHA256 11d316a549a5c95b93a9ed98fc580dafac8bfeae3a40c435639662a2c047d64e. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData42; original SHA256 709c0bd6914ee1c1181f151840da49be63f2fae2e4de4d163170b17c5dc72c11. -/

namespace D1Bound5.PairGraphPrepared42
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared42

/- Preserved body from D1Bound5.SmallPairGraphClosure42; original SHA256 2f7911b205f189a4b5a1cc26fedf3608921021ba95e39dc0344768ee9a21263e. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared42





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData42; original SHA256 245fb4473f619e3d17a60299f8662a982d483bd8ab8f2abc1366b272dd797def. -/

namespace D1Bound5.PairSelectedPrepared42
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared42

/- Preserved body from D1Bound5.SmallPairLightAssembly42; original SHA256 60c90a5f9d67d181917899dbdbbad52af21334e0b65779e96864677d03075657. -/

namespace D1Bound5.PairLightPrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared42.left_checked :
    pairIndependentBool smallPairSieve_1_3 (pairSplitByMask smallPairLarge_42 PairGraphPrepared42.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared42

/- Preserved body from D1Bound5.SmallPairGraphTriangle42; original SHA256 91c579c9ca406a72e9bd3b12d424418d47a488728036d60bd1046b2dca9865fe. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData42; original SHA256 fe2f13df896894ce55ebbe0d8a39f9ac40b2578d241debfd77f1b8603357b039. -/
end
