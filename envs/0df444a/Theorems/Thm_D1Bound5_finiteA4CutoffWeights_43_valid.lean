-- Prove2me | Theorems.Thm_D1Bound5_finiteA4CutoffWeights_43_valid
-- name    : D1Bound5.finiteA4CutoffWeights_43_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:17.424858+00:00
-- url     : https://prove2.me/theorems/74176056-f230-4ec3-99ef-2d1ded02209f
-- title:
--   Finite A4Cutoff Weights 43 valid
-- statement:
--   Auxiliary result `finiteA4CutoffWeights_43_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallA4FixedArithmetic.lean, lines 403-407, SHA-256 5dd4aa68b22d8a4e1c6984770870f955818408707c7af81799468b13acd90c7f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA4FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallA4FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/- Each exact square certificate evaluates the actual divided A4 root
coefficient in the quadratic integer ring before taking its field norm.
It then checks the printed M4 with a strict rational row-sum comparison. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0















































































































































































theorem _root_.D1Bound5.finiteA4CutoffWeights_43_valid :
    FiniteA4FixedBound oneSmallCutoffRow_43.triple.anchorA
      oneSmallCutoffRow_43.triple.anchorB oneSmallCutoffRow_43.M4
      finiteA4CutoffWeights_43 := by sorry























































end D1Bound5
end
