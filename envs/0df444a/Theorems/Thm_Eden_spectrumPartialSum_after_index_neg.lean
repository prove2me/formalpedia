-- Prove2me | Theorems.Thm_Eden_spectrumPartialSum_after_index_neg
-- name    : Eden.spectrumPartialSum_after_index_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:12.097223+00:00
-- url     : https://prove2.me/theorems/54842467-fcf8-4472-863e-d4878e4aeaa3
-- title:
--   Eden: spectrum Partial Sum after index neg
-- statement:
--   The Eden construction uses the spectrum Partial Sum after index neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L68-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L68-L71

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.spectrumPartialSum_after_index_neg {a : Fin 5 → ℝ} {k : ℕ}
    (hk : kaplanYorkeIndex a < k) (hk₅ : k ≤ 5) : spectrumPartialSum a k < 0 := by sorry
