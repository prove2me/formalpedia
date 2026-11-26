-- Prove2me | Theorems.Thm_Eden_volumeDefect_integrand_nonneg
-- name    : Eden.volumeDefect_integrand_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:29:54.957533+00:00
-- url     : https://prove2.me/theorems/d32871ed-3280-5502-a165-e44d1dc12db2
-- title:
--   Eden: volume Defect integrand nonneg
-- statement:
--   The Eden construction uses the volume Defect integrand nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L44-L47
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L44-L47

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.volumeDefect_integrand_nonneg (c τ : ℝ) (p : PhaseSpace) :
    0 ≤ (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2 := by sorry
