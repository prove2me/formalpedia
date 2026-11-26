-- Prove2me | Theorems.Thm_Eden_continuousOn_volumeDefect_integrand
-- name    : Eden.continuousOn_volumeDefect_integrand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:29:52.206021+00:00
-- url     : https://prove2.me/theorems/b13799f9-dd02-5399-b117-3924a7962020
-- title:
--   Eden: continuous On volume Defect integrand
-- statement:
--   The Eden construction uses the continuous On volume Defect integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L36-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VolumeConsequences.lean#L36-L42

import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_VolumeConsequences
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.continuousOn_volumeDefect_integrand (c : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun τ => (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2) (Set.Ici 0) := by sorry
