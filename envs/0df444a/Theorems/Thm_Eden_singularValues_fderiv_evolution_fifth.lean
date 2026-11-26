-- Prove2me | Theorems.Thm_Eden_singularValues_fderiv_evolution_fifth
-- name    : Eden.singularValues_fderiv_evolution_fifth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:46.979812+00:00
-- url     : https://prove2.me/theorems/fb85e3d7-7351-59d6-b7cd-8885396d2d9e
-- title:
--   Eden: singular Values fderiv evolution fifth
-- statement:
--   Mathlib indexes the five ambient singular values from zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L89-L108
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorBounds.lean#L89-L108

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValues_fderiv_evolution_fifth {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    (fderiv ℝ (evolution c t) p).toLinearMap.singularValues 4 = Real.exp (-c * t) := by sorry
