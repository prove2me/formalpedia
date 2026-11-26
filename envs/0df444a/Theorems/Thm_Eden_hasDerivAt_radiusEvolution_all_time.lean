-- Prove2me | Theorems.Thm_Eden_hasDerivAt_radiusEvolution_all_time
-- name    : Eden.hasDerivAt_radiusEvolution_all_time
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:40:46.799995+00:00
-- url     : https://prove2.me/theorems/6196d391-c985-4213-ae8d-62e331fee944
-- title:
--   Eden: has Deriv At radius Evolution all time
-- statement:
--   The Eden construction uses the has Deriv At radius Evolution all time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L127-L150
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L127-L150

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_radiusEvolution_all_time (t : ℝ) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₂ : r ≤ Real.sqrt 2) :
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t := by sorry
