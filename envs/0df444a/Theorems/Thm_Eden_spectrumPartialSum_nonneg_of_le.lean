-- Prove2me | Theorems.Thm_Eden_spectrumPartialSum_nonneg_of_le
-- name    : Eden.spectrumPartialSum_nonneg_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:33.767739+00:00
-- url     : https://prove2.me/theorems/7f97d69b-cd0a-4c25-bd1e-456531ccc1c7
-- title:
--   Eden: spectrum Partial Sum nonneg of le
-- statement:
--   The Eden construction uses the spectrum Partial Sum nonneg of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L21-L46
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L21-L46

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumPartialSum_nonneg_of_le {a : Fin 5 → ℝ} (ha : Antitone a)
    {k j : ℕ} (hkj : k ≤ j) (hj : j ≤ 5) (hs : 0 ≤ spectrumPartialSum a j) :
    0 ≤ spectrumPartialSum a k := by sorry
