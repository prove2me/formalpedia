-- Prove2me | Theorems.Thm_Eden_norm_exterior_map_le_singularValueFunction
-- name    : Eden.norm_exterior_map_le_singularValueFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:36:17.962601+00:00
-- url     : https://prove2.me/theorems/6759f805-fbf5-43e7-971d-1b2e816c434c
-- title:
--   Eden: norm exterior map le singular Value Function
-- statement:
--   The Eden construction uses the norm exterior map le singular Value Function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L41-L60
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L41-L60

import Definitions.Def_Eden_ExteriorGram
import Definitions.Def_Eden_ExteriorSingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.norm_exterior_map_le_singularValueFunction {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorPower.map k A v‖ ≤ singularValueFunction A k * ‖v‖ := by sorry
