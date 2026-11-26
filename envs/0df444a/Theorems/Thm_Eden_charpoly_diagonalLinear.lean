-- Prove2me | Theorems.Thm_Eden_charpoly_diagonalLinear
-- name    : Eden.charpoly_diagonalLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:14.119881+00:00
-- url     : https://prove2.me/theorems/3c86dba7-4cbf-5ef3-a2ed-b0e3659f4dd0
-- title:
--   Eden: charpoly diagonal Linear
-- statement:
--   The Eden construction uses the charpoly diagonal Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L42-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L42-L45

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.charpoly_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).charpoly = ∏ i : Fin 5, (X - C (d i)) := by sorry
