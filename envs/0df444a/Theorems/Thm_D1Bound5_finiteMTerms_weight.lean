-- Prove2me | Theorems.Thm_D1Bound5_finiteMTerms_weight
-- name    : D1Bound5.finiteMTerms_weight
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:25:00.937556+00:00
-- url     : https://prove2.me/theorems/7875e185-6027-4cbc-9865-a347d9abc46d
-- title:
--   Finite MTerms weight
-- statement:
--   The complete finite row certificate; it requires no norm or analytic assumption. In row zero the exact sum is38400, in the other rows169728.
-- source:
--   D1Bound5/FiniteMMatrix.lean, lines 150-154, SHA-256 8af7f9699b9fc84a48e57a25795d84c9aefe6f4ade8e20a65b9b82216db511c9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
namespace D1Bound5






















theorem _root_.D1Bound5.finiteMTerms_weight (i : Fin 4) :
    (∑ j : Fin 3, ((finiteMTerms i j.succ).map finiteMTermWeight).sum) ≤ 169728 := by sorry






end D1Bound5
end
