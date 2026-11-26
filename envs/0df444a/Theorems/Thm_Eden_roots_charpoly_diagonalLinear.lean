-- Prove2me | Theorems.Thm_Eden_roots_charpoly_diagonalLinear
-- name    : Eden.roots_charpoly_diagonalLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:16.450843+00:00
-- url     : https://prove2.me/theorems/285483d9-f5e5-57c5-b9c6-ff90bc95a8d5
-- title:
--   Eden: roots charpoly diagonal Linear
-- statement:
--   The Eden construction uses the roots charpoly diagonal Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L47-L51
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L47-L51

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.roots_charpoly_diagonalLinear (d : PhaseSpace) :
    (diagonalLinear d).charpoly.roots = Finset.univ.val.map (fun i => d i) := by sorry
