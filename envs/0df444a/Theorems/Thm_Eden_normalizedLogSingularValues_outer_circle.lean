-- Prove2me | Theorems.Thm_Eden_normalizedLogSingularValues_outer_circle
-- name    : Eden.normalizedLogSingularValues_outer_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:34.8605+00:00
-- url     : https://prove2.me/theorems/95764f5c-3e81-47b1-a070-bed7a393f449
-- title:
--   Eden: normalized Log Singular Values outer circle
-- statement:
--   The ordered normalized finite-time rates on either outer periodic circle.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L135-L144
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L135-L144

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.normalizedLogSingularValues_outer_circle {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    normalizedLogSingularValues c t p = ![0, -2, -2, -4, -c] := by sorry
