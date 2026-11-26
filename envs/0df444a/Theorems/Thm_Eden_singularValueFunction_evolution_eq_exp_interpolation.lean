-- Prove2me | Theorems.Thm_Eden_singularValueFunction_evolution_eq_exp_interpolation
-- name    : Eden.singularValueFunction_evolution_eq_exp_interpolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:43.692794+00:00
-- url     : https://prove2.me/theorems/56a8ff9e-cdee-496e-848e-78e18a9fbfb3
-- title:
--   Eden: singular Value Function evolution eq exp interpolation
-- statement:
--   The Eden construction uses the singular Value Function evolution eq exp interpolation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L48-L59
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L48-L59

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.singularValueFunction_evolution_eq_exp_interpolation (c : ℝ) {t : ℝ}
    (ht : 0 < t) (p : PhaseSpace) (d : ℝ) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (t * spectrumInterpolation (normalizedLogSingularValues c t p) d) := by sorry
