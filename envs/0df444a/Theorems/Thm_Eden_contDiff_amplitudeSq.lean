-- Prove2me | Theorems.Thm_Eden_contDiff_amplitudeSq
-- name    : Eden.contDiff_amplitudeSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:15.638708+00:00
-- url     : https://prove2.me/theorems/ad535d56-06a6-4498-a96c-a7734348c4be
-- title:
--   Eden: cont Diff amplitude Sq
-- statement:
--   The Eden construction uses the cont Diff amplitude Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L15-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L15-L28

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiff_amplitudeSq {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (amplitudeSq t) := by sorry
