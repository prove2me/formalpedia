-- Prove2me | Theorems.Thm_D1Bound5_finiteA3CutoffWeights_54_valid
-- name    : D1Bound5.finiteA3CutoffWeights_54_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:45:24.737572+00:00
-- url     : https://prove2.me/theorems/b3459c65-b52b-4eff-a723-7a70915b78af
-- title:
--   Finite A3Cutoff Weights 54 valid
-- statement:
--   Auxiliary result `finiteA3CutoffWeights_54_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallA3FixedArithmetic.lean, lines 502-506, SHA-256 1371295acd55c4fcf4c4d86e929716dae805c1b51e26253ec589fcde6559edfd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA3FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallA3FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/- Each exact square certificate evaluates the actual divided A3 root
coefficient in the quadratic integer ring before taking its field norm.
It then checks the printed M3 with a strict rational row-sum comparison. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0



























































































































































































































theorem _root_.D1Bound5.finiteA3CutoffWeights_54_valid :
    FiniteA3FixedBound oneSmallCutoffRow_54.triple.anchorA
      oneSmallCutoffRow_54.triple.anchorB oneSmallCutoffRow_54.M3
      finiteA3CutoffWeights_54 := by sorry











end D1Bound5
end
