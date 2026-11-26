-- Prove2me | Theorems.Thm_Eden_adjoint_planarDiagonal
-- name    : Eden.adjoint_planarDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:49.391933+00:00
-- url     : https://prove2.me/theorems/c560ae95-c767-565c-9e34-c2ce0c4099bd
-- title:
--   Eden: adjoint planar Diagonal
-- statement:
--   The Eden construction uses the adjoint planar Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L22-L27
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L22-L27

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.adjoint_planarDiagonal (d : PlanarSpace) :
    (planarDiagonal d).adjoint = planarDiagonal d := by sorry
