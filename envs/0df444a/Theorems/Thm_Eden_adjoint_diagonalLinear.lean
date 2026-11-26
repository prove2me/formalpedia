-- Prove2me | Theorems.Thm_Eden_adjoint_diagonalLinear
-- name    : Eden.adjoint_diagonalLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:09.626878+00:00
-- url     : https://prove2.me/theorems/a22764a1-53de-48da-8084-df55c7d1ddbe
-- title:
--   Eden: adjoint diagonal Linear
-- statement:
--   The Eden construction uses the adjoint diagonal Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L22-L27
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L22-L27

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.adjoint_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).adjoint = diagonalLinear d := by sorry
