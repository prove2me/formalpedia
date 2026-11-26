-- Prove2me | Theorems.Thm_Eden_volumeDefect_eq_integral_evolution
-- name    : Eden.volumeDefect_eq_integral_evolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:30:43.018692+00:00
-- url     : https://prove2.me/theorems/78a4cd1c-bca5-5b6e-8596-ecd8d958545d
-- title:
--   Eden: volume Defect eq integral evolution
-- statement:
--   This is exactly the manuscript's integral along the trajectory.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L84-L96
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L84-L96

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.volumeDefect_eq_integral_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    volumeDefect t p = ∫ τ in (0 : ℝ)..t,
      ((radiusSq₁ (evolution c τ p) - 1) ^ 2 +
        (radiusSq₂ (evolution c τ p) - 1) ^ 2) := by sorry
