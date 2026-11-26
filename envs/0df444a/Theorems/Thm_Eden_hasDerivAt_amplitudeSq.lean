-- Prove2me | Theorems.Thm_Eden_hasDerivAt_amplitudeSq
-- name    : Eden.hasDerivAt_amplitudeSq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:49.451198+00:00
-- url     : https://prove2.me/theorems/fb531a6f-b625-5bed-b6fa-60f89b35aeff
-- title:
--   Eden: has Deriv At amplitude Sq
-- statement:
--   The Eden construction uses the has Deriv At amplitude Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L73-L76
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L73-L76

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden

theorem Eden.hasDerivAt_amplitudeSq {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => amplitudeSq τ s)
      (2 * q (squaredRadiusEvolution t s) * amplitudeSq t s) t := by sorry
