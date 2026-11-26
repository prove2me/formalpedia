-- Prove2me | Theorems.Thm_Eden_singularValueFunction_evolution_on_four_five
-- name    : Eden.singularValueFunction_evolution_on_four_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:52.638827+00:00
-- url     : https://prove2.me/theorems/4ab0adb4-857d-5f1c-9758-9a3efaba539e
-- title:
--   Eden: singular Value Function evolution on four five
-- statement:
--   The Eden construction uses the singular Value Function evolution on four five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L17-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L17-L31

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_evolution_on_four_five {c t d : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (4 * t - 6 * volumeDefect t p - c * t * (d - 4)) := by sorry
