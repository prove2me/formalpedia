-- Prove2me | Theorems.Thm_D1Bound5_mixedAdjEnvelope_symmetric
-- name    : D1Bound5.mixedAdjEnvelope_symmetric
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:29.59549+00:00
-- url     : https://prove2.me/theorems/bf43498f-079d-4d2f-940b-e21564802ab0
-- title:
--   Mixed Adj Envelope symmetric
-- statement:
--   Auxiliary result `mixedAdjEnvelope_symmetric` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/MixedAdjugateEnvelope.lean, lines 19-32, SHA-256 f452ef49f0d5283120370edce69efeffabb48f22241346c2ec9821c339c43131. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_D1Bound5_MixedAdjugateEnvelope_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





theorem _root_.D1Bound5.mixedAdjEnvelope_symmetric (i j : Fin 4) :
    mixedAdjEnvelope i j = mixedAdjEnvelope j i := by sorry





end D1Bound5
end
