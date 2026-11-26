-- Prove2me | Theorems.Thm_Eden_diagonalLinear_basis
-- name    : Eden.diagonalLinear_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:13.063071+00:00
-- url     : https://prove2.me/theorems/4bd68983-28ac-4d7f-84b5-793fd5bc340a
-- title:
--   Eden: diagonal Linear basis
-- statement:
--   The Eden construction uses the diagonal Linear basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L41-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean#L41-L49

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.diagonalLinear_basis (d : PhaseSpace) (j : Fin 5) :
    diagonalLinear d (EuclideanSpace.basisFun (Fin 5) ℝ j) =
      d j • EuclideanSpace.basisFun (Fin 5) ℝ j := by sorry
