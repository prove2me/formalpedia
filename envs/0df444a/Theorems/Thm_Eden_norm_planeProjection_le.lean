-- Prove2me | Theorems.Thm_Eden_norm_planeProjection_le
-- name    : Eden.norm_planeProjection_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:44.642918+00:00
-- url     : https://prove2.me/theorems/00384de0-ef33-4b07-8265-53a6a65a3a46
-- title:
--   Eden: norm plane Projection le
-- statement:
--   The Eden construction uses the norm plane Projection le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L30-L35
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InstabilityGeometry.lean#L30-L35

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.norm_planeProjection_le (j : Fin 2) (p : PhaseSpace) :
    ‖planeProjection j p‖ ≤ ‖p‖ := by sorry
