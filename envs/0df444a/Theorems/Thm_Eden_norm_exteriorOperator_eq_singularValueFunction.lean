-- Prove2me | Theorems.Thm_Eden_norm_exteriorOperator_eq_singularValueFunction
-- name    : Eden.norm_exteriorOperator_eq_singularValueFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:36:36.662024+00:00
-- url     : https://prove2.me/theorems/4ce58656-e49d-4dd8-a5dc-4fdd8ddde026
-- title:
--   Eden: norm exterior Operator eq singular Value Function
-- statement:
--   For every real ambient linear map, omega_k is the exterior
--   operator norm. Singular maps, ties and the endpoint degrees are included.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L64-L75
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L64-L75

import Definitions.Def_Eden_ExteriorGram
import Definitions.Def_Eden_ExteriorSingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.norm_exteriorOperator_eq_singularValueFunction {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ‖exteriorOperator k A‖ = singularValueFunction A k := by sorry
