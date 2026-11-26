-- Prove2me | Theorems.Thm_Eden_squaredRadiusEvolution_mem_upper_interval
-- name    : Eden.squaredRadiusEvolution_mem_upper_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:47.955988+00:00
-- url     : https://prove2.me/theorems/afc3f2b2-117d-4696-9f40-84b5d38e4edc
-- title:
--   Eden: squared Radius Evolution mem upper interval
-- statement:
--   The Eden construction uses the squared Radius Evolution mem upper interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L53-L61
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L53-L61

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.squaredRadiusEvolution_mem_upper_interval (t : ℝ) {s : ℝ}
    (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2) :
    squaredRadiusEvolution t s ∈ Set.Icc 1 2 := by sorry
