-- Prove2me | Theorems.Thm_Eden_singularValueFunction_evolution_above_target
-- name    : Eden.singularValueFunction_evolution_above_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:35.878892+00:00
-- url     : https://prove2.me/theorems/3f2e28ef-fc12-59ab-8f77-78319627db7a
-- title:
--   Eden: singular Value Function evolution above target
-- statement:
--   The Eden construction uses the singular Value Function evolution above target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L45-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L45-L56

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_evolution_above_target {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (-6 * volumeDefect t p - c * t * (d - targetDimension c)) := by sorry
