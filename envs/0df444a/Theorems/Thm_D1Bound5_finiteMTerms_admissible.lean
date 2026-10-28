-- Prove2me | Theorems.Thm_D1Bound5_finiteMTerms_admissible
-- name    : D1Bound5.finiteMTerms_admissible
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:42:38.871526+00:00
-- url     : https://prove2.me/theorems/4957c42e-0ae3-4ef8-918e-5e8d9f25bc91
-- title:
--   Finite MTerms admissible
-- statement:
--   Every root-column monomial has the required anchor and terminal weights.
-- source:
--   D1Bound5/FiniteMMatrix.lean, lines 145-148, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
namespace D1Bound5




















theorem _root_.D1Bound5.finiteMTerms_admissible (i : Fin 4) (j : Fin 3) :
    ∀ t ∈ finiteMTerms i j.succ, finiteMTermAdmissible t := by sorry








end D1Bound5
end
