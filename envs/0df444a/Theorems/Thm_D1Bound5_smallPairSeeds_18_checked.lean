-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_18_checked
-- name    : D1Bound5.smallPairSeeds_18_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:26.438204+00:00
-- url     : https://prove2.me/theorems/e0039b13-d427-4f87-b14a-25cb59438410
-- title:
--   Small Pair Seeds 18 checked
-- statement:
--   Auxiliary result `smallPairSeeds_18_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphData18.lean, lines 1089-1092, SHA-256 607cc07aa1cd551526577bfbf390359252907b1bc8f7da79eed276a108fc5cf6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData18_Definitions_002

section
/- Preserved body from D1Bound5.SmallPairGraphInputs18; original SHA256 4e0725200849e7f0c12ef94e263f2be18996f451cd593d925ec9f29bb2a716a0. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared18



end PairGraphPrepared18
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic18; original SHA256 3d589e3aa318c05e5333e2c45ed6b6cb1c3736cdc9eef27e311f608a7ce46881. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_18_checked :
    pairSeedsCoveredBool smallPairA_18 smallPairB_18
      seedRootDisk_1_1 smallPairClosure_18 = true := by sorry





end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData18; original SHA256 1e4150b9590e501b712561d8dd52f7fc7ac226e8120fa232fe7904b8afaea1fd. -/

namespace D1Bound5.PairGraphPrepared18
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared18

/- Preserved body from D1Bound5.SmallPairGraphClosure18; original SHA256 c3754b82b865e39e2355e8ca10bb7ba465f2279245ad2127a256bbedaa75a42e. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared18





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData18; original SHA256 f3a84b4213d6f0a398b7ecd3fc887419ba7d6b8290948add80502d384df2326e. -/

namespace D1Bound5.PairSelectedPrepared18
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared18

/- Preserved body from D1Bound5.SmallPairLightAssembly18; original SHA256 d2665eb2e71fd282244faf1e888b26ea35b39fb9baba72b9f752529dbec2eb97. -/

namespace D1Bound5.PairLightPrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared18

/- Preserved body from D1Bound5.SmallPairGraphTriangle18; original SHA256 a5c1b3cbabaf741966fbe847305701bd48e5ff27797c83035dbef150d247c2e0. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData18; original SHA256 aff729333a9970d9f0bc4183ef1983b93dab7af2874ec8177adfca29b55a32b4. -/
end
