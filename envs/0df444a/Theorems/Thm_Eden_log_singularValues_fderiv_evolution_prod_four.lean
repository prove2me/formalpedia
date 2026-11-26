-- Prove2me | Theorems.Thm_Eden_log_singularValues_fderiv_evolution_prod_four
-- name    : Eden.log_singularValues_fderiv_evolution_prod_four
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:30:04.226287+00:00
-- url     : https://prove2.me/theorems/7f37792d-547d-401b-990a-56c039333b7d
-- title:
--   Eden: log singular Values fderiv evolution prod four
-- statement:
--   The logarithm of the product of the four largest ordered ambient singular
--   values, on A for c>=4 and t>=0, equals the exact integrated rate.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L51-L55
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L51-L55

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.log_singularValues_fderiv_evolution_prod_four {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    Real.log (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      4 * t - 6 * volumeDefect t p := by sorry
