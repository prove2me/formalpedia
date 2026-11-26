-- Prove2me | Theorems.Thm_Eden_norm_exterior_map_isometry
-- name    : Eden.norm_exterior_map_isometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:43.786896+00:00
-- url     : https://prove2.me/theorems/385fb8d1-f623-473e-b5ce-7187c9550f0d
-- title:
--   Eden: norm exterior map isometry
-- statement:
--   The exterior map of a Euclidean isometry preserves the canonical
--   exterior norm, in every exterior degree, including zero and degrees above 5.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L66-L82
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L66-L82

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.norm_exterior_map_isometry (k : ℕ) (U : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) : ‖exteriorPower.map k U.toLinearMap v‖ = ‖v‖ := by sorry
