-- Prove2me | Theorems.Thm_Eden_singularValueFunction_evolution_above_target_lt_one
-- name    : Eden.singularValueFunction_evolution_above_target_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:04.600843+00:00
-- url     : https://prove2.me/theorems/05796b97-3314-4bf5-b91a-8a04375af8b5
-- title:
--   Eden: singular Value Function evolution above target lt one
-- statement:
--   The Eden construction uses the singular Value Function evolution above target lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L58-L65
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L58-L65

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_evolution_above_target_lt_one {c t d : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd : targetDimension c < d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d < 1 := by sorry
