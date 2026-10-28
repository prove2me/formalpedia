-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_2_checked
-- name    : D1Bound5.smallPairSeeds_2_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:18.878288+00:00
-- url     : https://prove2.me/theorems/3cf1da60-6546-4912-a682-6450b690bb63
-- title:
--   Small Pair Seeds 2 checked
-- statement:
--   Auxiliary result `smallPairSeeds_2_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphData2.lean, lines 869-872, SHA-256 be08008a0ad80b33a5853a5240bd17aa588c523ee4ff90f53bde4787f4fb0943. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphData2_Definitions_001

section
/- Preserved body from D1Bound5.SmallPairGraphInputs2; original SHA256 05c6eac538f8497cd3a821770526ca8706d00a25abdc81b4c26cfd4d1fb29b57. -/

namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared2



end PairGraphPrepared2
end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphArithmetic2; original SHA256 26154516f673902cc1e3bce80054f0c96e08d80a543d1e1f2882f177302acaf7. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_2_checked :
    pairSeedsCoveredBool smallPairA_2 smallPairB_2
      seedRootDisk_0_1 smallPairClosure_2 = true := by sorry





end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphWitnessData2; original SHA256 f319a0bdaefa48f1a9f3ae5ceb65656c94c041b0fa290e14cab6856d8341c7fb. -/

namespace D1Bound5.PairGraphPrepared2
set_option maxRecDepth 100000









end D1Bound5.PairGraphPrepared2

/- Preserved body from D1Bound5.SmallPairGraphClosure2; original SHA256 6c3d39e00759e54ecfe739fe7c0b0c438ed702899f4932797158545d8d3f914b. -/

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared2





end D1Bound5

/- Preserved body from D1Bound5.SmallPairRawSelectedData2; original SHA256 bd14d335ba3742940ee6255966b2aa93923682ac39e18375e9a9ee7870d1dc4f. -/

namespace D1Bound5.PairSelectedPrepared2
set_option maxRecDepth 100000









end D1Bound5.PairSelectedPrepared2

/- Preserved body from D1Bound5.SmallPairLightAssembly2; original SHA256 28e25096d2fda97cfe2f853e3f3dc8734674d85d678e091170cdd16eaf988ed7. -/

namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0



















end D1Bound5.PairLightPrepared2

/- Preserved body from D1Bound5.SmallPairGraphTriangle2; original SHA256 304600336a461f07462df8aa2968c65908970f7e5cd79d6981f86853f6ac6e7d. -/

namespace D1Bound5
set_option maxRecDepth 100000



end D1Bound5

/- Preserved body from D1Bound5.SmallPairGraphData2; original SHA256 89e5d1cc4246d5ec20132684b3f2d13a6ac263401e770195eef0c09fa478e927. -/
end
