-- Prove2me | Theorems.Thm_Eden_amplitudeSq_at_zero
-- name    : Eden.amplitudeSq_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:50.7295+00:00
-- url     : https://prove2.me/theorems/43df97e0-55dc-4538-8012-35f0a100f12f
-- title:
--   Eden: amplitude Sq at zero
-- statement:
--   The Eden construction uses the amplitude Sq at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L127-L130
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L127-L130

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.amplitudeSq_at_zero (t : ℝ) :
    amplitudeSq t 0 = Real.exp (-4 * t) := by sorry
