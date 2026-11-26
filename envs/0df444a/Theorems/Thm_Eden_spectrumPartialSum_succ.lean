-- Prove2me | Theorems.Thm_Eden_spectrumPartialSum_succ
-- name    : Eden.spectrumPartialSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:57.099832+00:00
-- url     : https://prove2.me/theorems/9a3322d3-70da-5d65-b65c-6224edccb23b
-- title:
--   Eden: spectrum Partial Sum succ
-- statement:
--   The Eden construction uses the spectrum Partial Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L30-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L30-L32

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.spectrumPartialSum_succ (a : Fin 5 → ℝ) (k : ℕ) :
    spectrumPartialSum a (k + 1) = spectrumPartialSum a k + spectrumEntry a k := by sorry
