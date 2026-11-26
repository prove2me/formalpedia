-- Prove2me | Theorems.Thm_Eden_amplitudeSq_pos
-- name    : Eden.amplitudeSq_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:52.895148+00:00
-- url     : https://prove2.me/theorems/daf55f74-f59e-52ef-93eb-35f63083a71d
-- title:
--   Eden: amplitude Sq pos
-- statement:
--   The Eden construction uses the amplitude Sq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L67-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L67-L71

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.amplitudeSq_pos {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < amplitudeSq t s := by sorry
