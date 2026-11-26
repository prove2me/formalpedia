-- Prove2me | Theorems.Thm_Eden_singularValues_fderiv_evolution_prod_four_eq_iff
-- name    : Eden.singularValues_fderiv_evolution_prod_four_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:31:09.506497+00:00
-- url     : https://prove2.me/theorems/ef219433-f7b5-552d-a1d6-f5047faec942
-- title:
--   Eden: singular Values fderiv evolution prod four eq iff
-- statement:
--   The Eden construction uses the singular Values fderiv evolution prod four eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L152-L158
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeGrowth.lean#L152-L158

import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_VolumeGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValues_fderiv_evolution_prod_four_eq_iff {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor) :
    (∏ i : Fin 4, (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Real.exp (4 * t) ↔ p ∈ torus := by sorry
