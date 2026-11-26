-- Prove2me | Theorems.Thm_Eden_exponentSum_four_origin
-- name    : Eden.exponentSum_four_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:42.62396+00:00
-- url     : https://prove2.me/theorems/7e2e728b-5308-593b-b154-f27728bd15f8
-- title:
--   Eden: exponent Sum four origin
-- statement:
--   The Eden construction uses the exponent Sum four origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L45-L50
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L45-L50

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_origin {c : ℝ} (hc : 4 < c) :
    spectrumPartialSum (lyapunovExponent c 0) 4 = -8 := by sorry
