-- Prove2me | Theorems.Thm_Eden_exterior_map_diagonal_basis
-- name    : Eden.exterior_map_diagonal_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:18.843019+00:00
-- url     : https://prove2.me/theorems/8a952a91-8363-5350-b4a4-1c259cfb1653
-- title:
--   Eden: exterior map diagonal basis
-- statement:
--   The Eden construction uses the exterior map diagonal basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L51-L62
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L51-L62

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.exterior_map_diagonal_basis (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) :
    exteriorPower.map k (diagonalLinear d) (exteriorBasis k s) =
      exteriorFactor k d s • exteriorBasis k s := by sorry
