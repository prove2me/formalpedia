-- Prove2me | Theorems.Thm_Eden_toMatrix_planarDiagonal
-- name    : Eden.toMatrix_planarDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:56.29399+00:00
-- url     : https://prove2.me/theorems/40b55826-2176-4f8b-8077-63681c7e0bb2
-- title:
--   Eden: to Matrix planar Diagonal
-- statement:
--   The Eden construction uses the to Matrix planar Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L35-L40
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L35-L40

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.toMatrix_planarDiagonal (d : PlanarSpace) :
    (planarDiagonal d).toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis = Matrix.diagonal (fun i => d i) := by sorry
