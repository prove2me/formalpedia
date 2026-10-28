-- Prove2me | Theorems.Thm_D1Bound5_finiteP_height_scaled
-- name    : D1Bound5.finiteP_height_scaled
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:12.211988+00:00
-- url     : https://prove2.me/theorems/4267ddd7-3fc1-46de-a9cb-18b9d3c1049f
-- title:
--   Finite P height scaled
-- statement:
--   Auxiliary result `finiteP_height_scaled` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePHeight.lean, lines 144-156, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three



























theorem _root_.D1Bound5.finiteP_height_scaled (a b s c : ℂ) (hA : 1 ≤ ‖a‖)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) (hC : 200 ≤ ‖c‖)
    (i : Fin 4) :
    (101/100 : ℝ)*(∑ j, ‖finitePRootColumn a b s c i j‖) <
      2400*max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*‖c‖^2 := by sorry

end D1Bound5
end
