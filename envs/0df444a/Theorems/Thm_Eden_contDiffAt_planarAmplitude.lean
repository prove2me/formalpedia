-- Prove2me | Theorems.Thm_Eden_contDiffAt_planarAmplitude
-- name    : Eden.contDiffAt_planarAmplitude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:05.281532+00:00
-- url     : https://prove2.me/theorems/e6369c68-615f-533d-8c2c-57768f66536f
-- title:
--   Eden: cont Diff At planar Amplitude
-- statement:
--   The Eden construction uses the cont Diff At planar Amplitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L30-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L30-L32

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiffAt_planarAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (planarAmplitude t) s := by sorry
