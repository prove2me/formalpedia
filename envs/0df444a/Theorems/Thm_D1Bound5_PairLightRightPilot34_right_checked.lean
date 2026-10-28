-- Prove2me | Theorems.Thm_D1Bound5_PairLightRightPilot34_right_checked
-- name    : D1Bound5.PairLightRightPilot34.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:56.066288+00:00
-- url     : https://prove2.me/theorems/587c0eb0-4498-4132-a077-b225ac1dad3a
-- title:
--   Pair Light Right Pilot34 — right checked
-- statement:
--   Exactly the original right independent-class assertion, obtained only after the four concrete data equalities and the unconditional checker bridge.
-- source:
--   D1Bound5/SmallPairLightRightAssembly34.lean, lines 32-41, SHA-256 072449c92bc3ef8eba73611724528c1db9d7f492e613f915c09deb40362f8fe2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions

section
namespace D1Bound5.PairLightRightPilot34
set_option maxRecDepth 100000
set_option maxHeartbeats 0










theorem _root_.D1Bound5.PairLightRightPilot34.right_checked :
    pairIndependentBool smallPairSieve_1_2
      (pairSplitByMask smallPairLarge_34 PairGraphPrepared34.colors).2 = true := by sorry

end D1Bound5.PairLightRightPilot34
end
