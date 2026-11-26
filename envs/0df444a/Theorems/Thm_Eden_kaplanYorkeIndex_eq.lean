-- Prove2me | Theorems.Thm_Eden_kaplanYorkeIndex_eq
-- name    : Eden.kaplanYorkeIndex_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:09.832617+00:00
-- url     : https://prove2.me/theorems/086a596d-b4d5-4d34-bcb4-0ad2f9dbd6b0
-- title:
--   Eden: kaplan Yorke Index eq
-- statement:
--   The Eden construction uses the kaplan Yorke Index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L58-L66
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L58-L66

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeIndex_eq {a : Fin 5 → ℝ} {j : ℕ} (hj : j ≤ 5)
    (hs : 0 ≤ spectrumPartialSum a j)
    (hafter : ∀ k, j < k → k ≤ 5 → spectrumPartialSum a k < 0) :
    kaplanYorkeIndex a = j := by sorry
