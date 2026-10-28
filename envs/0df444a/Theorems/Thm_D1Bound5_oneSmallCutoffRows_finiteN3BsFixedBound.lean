-- Prove2me | Theorems.Thm_D1Bound5_oneSmallCutoffRows_finiteN3BsFixedBound
-- name    : D1Bound5.oneSmallCutoffRows_finiteN3BsFixedBound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:50:49.864899+00:00
-- url     : https://prove2.me/theorems/c767240c-a331-4309-9654-6762e737665b
-- title:
--   One Small Cutoff Rows finite N3Bs Fixed Bound
-- statement:
--   The actual printed fixed-triple rows have verified N3 coefficients on the bs anchor pair, evaluated before taking norms.
-- source:
--   D1Bound5/OneSmallN3BsFixedArithmetic.lean, lines 524-588, SHA-256 4f43bff1dfec8db0799fdf167ba9ac59a3ba3fbd4a2f46b730480076a61b255b. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteN3FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/- Exact evaluated N3 coefficient certificates on the bs anchors. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0






































































































































































































































theorem _root_.D1Bound5.oneSmallCutoffRows_finiteN3BsFixedBound (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 4 → ℚ,
      FiniteN3FixedBound r.triple.anchorB r.triple.anchorS r.Mbs w := by sorry

end D1Bound5
end
