-- Prove2me | Theorems.Thm_Eden_rates_at_stationary_radii
-- name    : Eden.rates_at_stationary_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:27.317922+00:00
-- url     : https://prove2.me/theorems/daa0b4f5-aa3d-57ed-9482-b87b4cbf8706
-- title:
--   Eden: rates at stationary radii
-- statement:
--   The complete rate values at the three stationary squared radii.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L61-L65
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Algebra.lean#L61-L65

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
set_option autoImplicit true
open Eden

theorem Eden.rates_at_stationary_radii :
    radialRate 0 = -2 ∧ tangentialRate 0 = -2 ∧
    radialRate 1 = 2 ∧ tangentialRate 1 = 0 ∧
    radialRate 2 = -4 ∧ tangentialRate 2 = 0 := by sorry
