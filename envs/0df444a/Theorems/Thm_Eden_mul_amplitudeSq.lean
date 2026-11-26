-- Prove2me | Theorems.Thm_Eden_mul_amplitudeSq
-- name    : Eden.mul_amplitudeSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:16.056062+00:00
-- url     : https://prove2.me/theorems/186bd654-dfc7-4018-8bea-dfc5ab30cb2d
-- title:
--   Eden: mul amplitude Sq
-- statement:
--   The Eden construction uses the mul amplitude Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L87-L89
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L87-L89

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.mul_amplitudeSq {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    s * amplitudeSq t s = squaredRadiusEvolution t s := by sorry
