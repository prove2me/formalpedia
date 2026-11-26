-- Prove2me | Theorems.Thm_Eden_singularValueFunction_evolution_at_target
-- name    : Eden.singularValueFunction_evolution_at_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:37.759254+00:00
-- url     : https://prove2.me/theorems/f9db703b-abc0-45c1-abd7-db6a975f5f72
-- title:
--   Eden: singular Value Function evolution at target
-- statement:
--   The Eden construction uses the singular Value Function evolution at target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L33-L43
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L33-L43

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_evolution_at_target {c t : ℝ}
    (hc : 4 < c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap (targetDimension c) =
      Real.exp (-6 * volumeDefect t p) := by sorry
