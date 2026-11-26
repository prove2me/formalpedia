-- Prove2me | Theorems.Thm_Eden_norm_planeProjection
-- name    : Eden.norm_planeProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:30.306473+00:00
-- url     : https://prove2.me/theorems/0e23bf7a-660b-4b7b-aa98-49b37ce2f3b6
-- title:
--   Eden: norm plane Projection
-- statement:
--   The Eden construction uses the norm plane Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L22-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L22-L28

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.norm_planeProjection (j : Fin 2) (p : PhaseSpace) :
    ‖planeProjection j p‖ = Real.sqrt (if j = 0 then radiusSq₁ p else radiusSq₂ p) := by sorry
