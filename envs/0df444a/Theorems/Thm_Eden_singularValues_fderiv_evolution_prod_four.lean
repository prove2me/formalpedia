-- Prove2me | Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four
-- name    : Eden.singularValues_fderiv_evolution_prod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:21.35679+00:00
-- url     : https://prove2.me/theorems/a003e262-607c-4780-bd4f-28fe8a806361
-- title:
--   Eden: singular Values fderiv evolution prod four
-- statement:
--   Product of the first four standard, descending ambient singular values.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L116-L143
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L116-L143

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValues_fderiv_evolution_prod_four {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t - 6 * volumeDefect t p) := by sorry
