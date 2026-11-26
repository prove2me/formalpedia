-- Prove2me | Theorems.Thm_Eden_kaplanYorkeIndex_le_dimension
-- name    : Eden.kaplanYorkeIndex_le_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:54.908277+00:00
-- url     : https://prove2.me/theorems/f4cfc85c-3e1a-546f-bfb8-b0fee390c32f
-- title:
--   Eden: kaplan Yorke Index le dimension
-- statement:
--   The Eden construction uses the kaplan Yorke Index le dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L48-L55
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L48-L55

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.kaplanYorkeIndex_le_dimension (a : Fin 5 → ℝ) :
    (kaplanYorkeIndex a : ℝ) ≤ kaplanYorkeDimension a := by sorry
