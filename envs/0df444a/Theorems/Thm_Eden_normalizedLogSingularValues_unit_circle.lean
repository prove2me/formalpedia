-- Prove2me | Theorems.Thm_Eden_normalizedLogSingularValues_unit_circle
-- name    : Eden.normalizedLogSingularValues_unit_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:30.929003+00:00
-- url     : https://prove2.me/theorems/3dfcfc72-3622-4e65-a725-b8e2a3466fb6
-- title:
--   Eden: normalized Log Singular Values unit circle
-- statement:
--   The ordered normalized finite-time rates on either unit periodic circle.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L123-L132
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L123-L132

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.normalizedLogSingularValues_unit_circle {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    normalizedLogSingularValues c t p = ![2, 0, -2, -2, -c] := by sorry
