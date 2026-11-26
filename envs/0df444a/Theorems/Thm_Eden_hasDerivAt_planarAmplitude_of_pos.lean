-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarAmplitude_of_pos
-- name    : Eden.hasDerivAt_planarAmplitude_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:00.538041+00:00
-- url     : https://prove2.me/theorems/b1cdf645-54e7-5458-9208-7d49a9dd8a9c
-- title:
--   Eden: has Deriv At planar Amplitude of pos
-- statement:
--   The planar amplitude has exactly the tangential logarithmic growth rate.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L90-L99
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarCalculus.lean#L90-L99

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden

theorem Eden.hasDerivAt_planarAmplitude_of_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) (hB : 0 < amplitudeSq t s) :
    HasDerivAt (fun τ => planarAmplitude τ s)
      (q (squaredRadiusEvolution t s) * planarAmplitude t s) t := by sorry
