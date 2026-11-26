-- Prove2me | Theorems.Thm_Eden_diagonalLinear_basisFun
-- name    : Eden.diagonalLinear_basisFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:21.195287+00:00
-- url     : https://prove2.me/theorems/e9cd7847-dc79-4cb6-b6ec-862d4ce706b8
-- title:
--   Eden: diagonal Linear basis Fun
-- statement:
--   The Eden construction uses the diagonal Linear basis Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L35-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L35-L42

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.diagonalLinear_basisFun (d : PhaseSpace) (i : Fin 5) :
    diagonalLinear d (EuclideanSpace.basisFun (Fin 5) ℝ i) =
      d i • EuclideanSpace.basisFun (Fin 5) ℝ i := by sorry
