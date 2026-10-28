-- Prove2me | Theorems.Thm_D1Bound5_symmetricFour_adjugate_formula
-- name    : D1Bound5.symmetricFour_adjugate_formula
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:44.34301+00:00
-- url     : https://prove2.me/theorems/5cf128cd-1201-4a25-a4e0-99dd11b1c872
-- title:
--   Symmetric Four adjugate formula
-- statement:
--   All sixteen cofactors of the symmetric zero-diagonal four-by-four matrix.
-- source:
--   D1Bound5/AdjugateCoverage.lean, lines 18-27, SHA-256 f2847afb95c8defcb8c59c5324b1cbe3904cb7236a7d79d7d2486bba6b9076b4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_AdjugateCoverage_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5






theorem _root_.D1Bound5.symmetricFour_adjugate_formula (x y z u v w : ℂ) :
    (symmetricFour x y z u v w).adjugate = symmetricFourAdj x y z u v w := by sorry





end D1Bound5
end
