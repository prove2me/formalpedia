-- Prove2me | Theorems.Thm_D1Bound5_finiteP_root_columns_norm_le
-- name    : D1Bound5.finiteP_root_columns_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:18:00.089461+00:00
-- url     : https://prove2.me/theorems/4cd03dff-2ec6-42bb-a455-2b620a390a53
-- title:
--   Finite P root columns norm le
-- statement:
--   Uniform actual root-column height, including the cancellation in H,V.
-- source:
--   D1Bound5/FinitePHeight.lean, lines 111-137, SHA-256 314dc2ce401e7d406d8613d27c9a6ab48d94b1783ab8ee80b2eda5b7bee22fae. Project: https://github.com/tomislav-math/d1-bound5-lean

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
























theorem _root_.D1Bound5.finiteP_root_columns_norm_le (a b s c : ℂ) (hA : 1 ≤ ‖a‖)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) (i : Fin 4) :
    (∑ j, ‖finitePRootColumn a b s c i j‖) ≤
      max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*(492+2424*‖c‖+2352*‖c‖^2) := by sorry





end D1Bound5
end
