-- Prove2me | Theorems.Thm_Eden_planarAmplitude_sq
-- name    : Eden.planarAmplitude_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:01.483369+00:00
-- url     : https://prove2.me/theorems/de99b5a9-c9bb-4ee7-b19c-85bae54f8f90
-- title:
--   Eden: planar Amplitude sq
-- statement:
--   The Eden construction uses the planar Amplitude sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L82-L84
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L82-L84

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden

theorem Eden.planarAmplitude_sq {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s ^ 2 = amplitudeSq t s := by sorry
