-- Prove2me | Theorems.Thm_Eden_mul_amplitudeSq_of_discriminant_pos
-- name    : Eden.mul_amplitudeSq_of_discriminant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:58.209362+00:00
-- url     : https://prove2.me/theorems/d0e7edcd-d701-50d6-a679-c9a292a2fd62
-- title:
--   Eden: mul amplitude Sq of discriminant pos
-- statement:
--   The Eden construction uses the mul amplitude Sq of discriminant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L73-L85
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L73-L85

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.mul_amplitudeSq_of_discriminant_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    s * amplitudeSq t s = squaredRadiusEvolution t s := by sorry
