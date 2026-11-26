-- Prove2me | Theorems.Thm_Eden_norm_exterior_map_singular_basis
-- name    : Eden.norm_exterior_map_singular_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:36:25.101885+00:00
-- url     : https://prove2.me/theorems/e438d443-5a3d-49eb-81b7-e7587006cf32
-- title:
--   Eden: norm exterior map singular basis
-- statement:
--   The Eden construction uses the norm exterior map singular basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L32-L39
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L32-L39

import Definitions.Def_Eden_ExteriorGram
import Definitions.Def_Eden_ExteriorSingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.norm_exterior_map_singular_basis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) :
    ‖exteriorPower.map k A (singularExteriorBasis k A s)‖ = selectedSingularProduct k A s := by sorry
