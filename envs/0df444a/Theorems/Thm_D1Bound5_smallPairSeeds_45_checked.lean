-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_45_checked
-- name    : D1Bound5.smallPairSeeds_45_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:24:54.405431+00:00
-- url     : https://prove2.me/theorems/0ea12ec9-4e3d-49c2-a016-0c7fed791247
-- title:
--   Small Pair Seeds 45 checked
-- statement:
--   Auxiliary result `smallPairSeeds_45_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphData45.lean, lines 863-866, SHA-256 373463e9b5600703d80d2d098967a3029ee41ff3c22f1bec44e1f0e5a4281fd2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData45_Definitions_001
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions

section
/- Preserved body from D1Bound5.SmallPairGraphInputs45; original SHA256 e005e2e8cd75649429508b44f8449f6119b1af70789808e26eb05b3deea835d1. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared45



end PairGraphPrepared45
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic45; original SHA256 3a94fa935fa21ad5943c323eba44b6f35df957553b7d8649176809e361d51776. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_45_checked :
    pairSeedsCoveredBool smallPairA_45 smallPairB_45
      seedRootDisk_1_5 smallPairClosure_45 = true := by sorry





end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData45; original SHA256 5f07a239e6e5d926162b0a89c88c4e5e19bf9ed2c077da34499a3eaf01573086. -/

namespace D1Bound5.PairGraphPrepared45
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared45

/- Preserved body from D1Bound5.SmallPairGraphClosure45; original SHA256 a8e126e0ea71de1ea4fb613714cd6df1bb0f1f365d315068cb7ca1965805c4b5. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared45





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData45; original SHA256 65ac4f5dfac9d6e9fbbc457210c34487e3fe2bc52c553f1bf2e8620e0971f157. -/

namespace D1Bound5.PairSelectedPrepared45
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared45

/- Preserved body from D1Bound5.SmallPairLightAssembly45; original SHA256 ca0792cbca80dc647182dd3f457cd828d94bd590ac4a226175f3d673683d7b8c. -/

namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared45

/- Preserved body from D1Bound5.SmallPairGraphTriangle45; original SHA256 350e1602c0b0fbb99542419ef70a981c0070ba309dfe2268bd9f355a70eb5aaa. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData45; original SHA256 0932d1428f25bf1fbddb795e60ed173381edd6d1ae54456d0fbf29b9282010db. -/
end
