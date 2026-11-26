-- Prove2me | Theorems.Thm_Eden_exponentSum_four_outer_circle
-- name    : Eden.exponentSum_four_outer_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:38.826569+00:00
-- url     : https://prove2.me/theorems/780b4f49-c9da-5fbe-8036-281f3487d7f3
-- title:
--   Eden: exponent Sum four outer circle
-- statement:
--   The Eden construction uses the exponent Sum four outer circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L31-L43
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L31-L43

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_outer_circle {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    spectrumPartialSum (lyapunovExponent c p) 4 = -8 := by sorry
