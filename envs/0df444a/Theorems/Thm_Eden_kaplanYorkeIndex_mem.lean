-- Prove2me | Theorems.Thm_Eden_kaplanYorkeIndex_mem
-- name    : Eden.kaplanYorkeIndex_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:34.166184+00:00
-- url     : https://prove2.me/theorems/e9ab5066-edc8-4e9c-90b2-97ad6b24ee90
-- title:
--   Eden: kaplan Yorke Index mem
-- statement:
--   The Eden construction uses the kaplan Yorke Index mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L47-L52
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L47-L52

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeIndex_mem (a : Fin 5 → ℝ) :
    kaplanYorkeIndex a ≤ 5 ∧ 0 ≤ spectrumPartialSum a (kaplanYorkeIndex a) := by sorry
