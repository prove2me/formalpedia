-- Prove2me | Theorems.Thm_Eden_vectorField_eq_zero_iff
-- name    : Eden.vectorField_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:35.890949+00:00
-- url     : https://prove2.me/theorems/c873b9b6-9df5-5cd8-be4b-d913e0f487f3
-- title:
--   Eden: vector Field eq zero iff
-- statement:
--   The origin is the unique equilibrium whenever the fifth-coordinate coefficient
--   is nonzero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L49-L74
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L49-L74

import Definitions.Def_Eden_RotationReturns
import Definitions.Def_Eden_PeriodicSets
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.vectorField_eq_zero_iff {c : ℝ} (hc : c ≠ 0) (p : PhaseSpace) :
    vectorField c p = 0 ↔ p = 0 := by sorry
