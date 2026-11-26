-- Prove2me | Theorems.Thm_Eden_norm_sq_exterior_map_diagonal
-- name    : Eden.norm_sq_exterior_map_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:33.729265+00:00
-- url     : https://prove2.me/theorems/871daba8-9cf1-5ec3-9a51-7a6b53cd732a
-- title:
--   Eden: norm sq exterior map diagonal
-- statement:
--   Squared norm of a diagonal exterior map in the canonical norm.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L93-L97
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L93-L97

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.norm_sq_exterior_map_diagonal (k : ℕ) (d : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorPower.map k (diagonalLinear d) v‖ ^ 2 =
      ∑ s : ExteriorIndex k, (exteriorFactor k d s * (exteriorBasis k).repr v s) ^ 2 := by sorry
