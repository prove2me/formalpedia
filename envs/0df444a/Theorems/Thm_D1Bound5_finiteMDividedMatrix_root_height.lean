-- Prove2me | Theorems.Thm_D1Bound5_finiteMDividedMatrix_root_height
-- name    : D1Bound5.finiteMDividedMatrix_root_height
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:00.283014+00:00
-- url     : https://prove2.me/theorems/2ac68587-9be8-4d11-be10-d32da8d4a7f0
-- title:
--   Finite MDivided Matrix root height
-- statement:
--   The complete actual divided M matrix satisfies a deliberately generous height bound. This avoids the manuscript's sharper geometric row estimates, while leaving ample room in its stated approximation constant.
-- source:
--   D1Bound5/FiniteMHeight.lean, lines 89-125, SHA-256 6928941a5a34ad2fa5a5df87a96078a75cfb91e880665ed0fbfc978d07ef85b6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions

section
namespace D1Bound5








theorem _root_.D1Bound5.finiteMDividedMatrix_root_height (a b s c : ℂ)
    (hB : 1 ≤ ‖b‖) (hab : ‖a‖ ≤ ‖b‖) (hbs : ‖b‖ ≤ ‖s‖)
    (hC : 1 ≤ ‖c‖) (i : Fin 4) :
    (∑ j : Fin 3, ‖finiteMDividedMatrix a b s c i j.succ‖) ≤
      169728*‖b‖^3*‖s‖^8*‖c‖^2 := by sorry

end D1Bound5
end
