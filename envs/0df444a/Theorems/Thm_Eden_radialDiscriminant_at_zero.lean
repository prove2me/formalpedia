-- Prove2me | Theorems.Thm_Eden_radialDiscriminant_at_zero
-- name    : Eden.radialDiscriminant_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:39.014558+00:00
-- url     : https://prove2.me/theorems/d7123aeb-3066-4be7-8cb6-5fc9783e79d1
-- title:
--   Eden: radial Discriminant at zero
-- statement:
--   The Eden construction uses the radial Discriminant at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L110-L112
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L110-L112

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radialDiscriminant_at_zero (t : ℝ) : radialDiscriminant t 0 = 1 := by sorry
