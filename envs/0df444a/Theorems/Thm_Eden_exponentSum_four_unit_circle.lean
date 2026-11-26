-- Prove2me | Theorems.Thm_Eden_exponentSum_four_unit_circle
-- name    : Eden.exponentSum_four_unit_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:01.832083+00:00
-- url     : https://prove2.me/theorems/61e97c39-ddc6-54cb-97f4-7e7d895f8a30
-- title:
--   Eden: exponent Sum four unit circle
-- statement:
--   The Eden construction uses the exponent Sum four unit circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L17-L29
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L17-L29

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_unit_circle {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    spectrumPartialSum (lyapunovExponent c p) 4 = -2 := by sorry
