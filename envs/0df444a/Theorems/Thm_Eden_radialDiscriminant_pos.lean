-- Prove2me | Theorems.Thm_Eden_radialDiscriminant_pos
-- name    : Eden.radialDiscriminant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:50.656306+00:00
-- url     : https://prove2.me/theorems/1744157c-4967-5668-8d02-ae56000b8394
-- title:
--   Eden: radial Discriminant pos
-- statement:
--   The Eden construction uses the radial Discriminant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L37-L43
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L37-L43

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radialDiscriminant_pos {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    0 < radialDiscriminant t s := by sorry
