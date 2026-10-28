-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared13_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared13.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:15:01.864238+00:00
-- url     : https://prove2.me/theorems/a92065e0-cf92-4cf7-b233-244dfaa83367
-- title:
--   Pair Light Prepared13 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared13.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphData13.lean, lines 3119-3121, SHA-256 ce54ed29f160af4c3bb99c63b017080e34e63ea3f6500c390bcd1d99ded43f67. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData13_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphData13_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_003

section
/- Preserved body from D1Bound5.SmallPairGraphInputs13; original SHA256 c5e162c4bc960250e92b15dd3d783468d049132d96b85979af9506d77a521f61. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared13



end PairGraphPrepared13
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic13; original SHA256 65049f6bec9c79d86936bd3deea19ec925d693c7048de9fb9e32c5bbcecaaa7e. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData13; original SHA256 556060a6b394aa67f85deaa77b5ff08b8016b064b2322a52df284b5ef8ed4787. -/

namespace D1Bound5.PairGraphPrepared13
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared13

/- Preserved body from D1Bound5.SmallPairGraphClosure13; original SHA256 81e59ccaa6115a892462e75edc02ea7716dfe2ceae2a7cdb305c8fad43165cad. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared13





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData13; original SHA256 c7a93e661ec2ce8824b6a499d24999a58d69a9e9ad5fac8fb832f9193941ad55. -/

namespace D1Bound5.PairSelectedPrepared13
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared13

/- Preserved body from D1Bound5.SmallPairLightAssembly13; original SHA256 e76013453eff7aaa9f79d4c825325e8205e5a5479ec026372abb2ecc94fc4549. -/

namespace D1Bound5.PairLightPrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared13.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_13 PairGraphPrepared13.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared13

/- Preserved body from D1Bound5.SmallPairGraphTriangle13; original SHA256 486dda3838b12341918f0571b2caa08b7fd29d98208b269f2b8d10573b84da87. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData13; original SHA256 12a849f4683eb3969e097c63c91d9f00719653bc181140cfce7f1a09a576ea58. -/
end
