-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarAmplitude
-- name    : Eden.hasDerivAt_planarAmplitude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:54.230485+00:00
-- url     : https://prove2.me/theorems/9df875e6-ea88-5d9b-9254-d500c197592c
-- title:
--   Eden: has Deriv At planar Amplitude
-- statement:
--   The Eden construction uses the has Deriv At planar Amplitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L101-L104
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L101-L104

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden

theorem Eden.hasDerivAt_planarAmplitude {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => planarAmplitude τ s)
      (q (squaredRadiusEvolution t s) * planarAmplitude t s) t := by sorry
