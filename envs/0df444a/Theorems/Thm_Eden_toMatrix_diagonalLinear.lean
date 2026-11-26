-- Prove2me | Theorems.Thm_Eden_toMatrix_diagonalLinear
-- name    : Eden.toMatrix_diagonalLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:11.250264+00:00
-- url     : https://prove2.me/theorems/b902b415-9a65-5d97-981b-43700c76502f
-- title:
--   Eden: to Matrix diagonal Linear
-- statement:
--   The Eden construction uses the to Matrix diagonal Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L35-L40
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L35-L40

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.toMatrix_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).toMatrix (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis = Matrix.diagonal (fun i => d i) := by sorry
