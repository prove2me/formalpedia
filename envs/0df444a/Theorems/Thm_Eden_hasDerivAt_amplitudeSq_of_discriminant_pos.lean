-- Prove2me | Theorems.Thm_Eden_hasDerivAt_amplitudeSq_of_discriminant_pos
-- name    : Eden.hasDerivAt_amplitudeSq_of_discriminant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:24.440623+00:00
-- url     : https://prove2.me/theorems/1796574a-3f80-59ee-8fed-b6b84a5b7f27
-- title:
--   Eden: has Deriv At amplitude Sq of discriminant pos
-- statement:
--   The time derivative of the squared amplitude, including initial radius zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L48-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L48-L71

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden

theorem Eden.hasDerivAt_amplitudeSq_of_discriminant_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    HasDerivAt (fun τ => amplitudeSq τ s)
      (2 * q (squaredRadiusEvolution t s) * amplitudeSq t s) t := by sorry
