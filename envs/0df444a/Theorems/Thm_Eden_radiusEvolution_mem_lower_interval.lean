-- Prove2me | Theorems.Thm_Eden_radiusEvolution_mem_lower_interval
-- name    : Eden.radiusEvolution_mem_lower_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:40:31.802793+00:00
-- url     : https://prove2.me/theorems/e127e2fc-81a3-5280-96e5-d449c8d51563
-- title:
--   Eden: radius Evolution mem lower interval
-- statement:
--   The Eden construction uses the radius Evolution mem lower interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L113-L117
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L113-L117

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radiusEvolution_mem_lower_interval (t : ℝ) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    radiusEvolution t r ∈ Set.Icc 0 1 := by sorry
