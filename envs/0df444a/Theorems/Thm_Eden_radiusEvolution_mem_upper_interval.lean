-- Prove2me | Theorems.Thm_Eden_radiusEvolution_mem_upper_interval
-- name    : Eden.radiusEvolution_mem_upper_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:34.490806+00:00
-- url     : https://prove2.me/theorems/c96aa8ae-73a7-517b-afa2-4d7577b005f1
-- title:
--   Eden: radius Evolution mem upper interval
-- statement:
--   The Eden construction uses the radius Evolution mem upper interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L119-L125
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L119-L125

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radiusEvolution_mem_upper_interval (t : ℝ) {r : ℝ}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ Real.sqrt 2) :
    radiusEvolution t r ∈ Set.Icc 1 (Real.sqrt 2) := by sorry
