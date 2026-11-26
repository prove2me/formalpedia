-- Prove2me | Theorems.Thm_Eden_le_kaplanYorkeIndex
-- name    : Eden.le_kaplanYorkeIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:20.795256+00:00
-- url     : https://prove2.me/theorems/cb00619a-e9b9-436a-b885-ca2e8512718a
-- title:
--   Eden: le kaplan Yorke Index
-- statement:
--   The Eden construction uses the le kaplan Yorke Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L54-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L54-L56

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.le_kaplanYorkeIndex {a : Fin 5 → ℝ} {k : ℕ} (hk : k ≤ 5)
    (hs : 0 ≤ spectrumPartialSum a k) : k ≤ kaplanYorkeIndex a := by sorry
