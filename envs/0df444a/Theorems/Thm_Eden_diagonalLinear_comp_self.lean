-- Prove2me | Theorems.Thm_Eden_diagonalLinear_comp_self
-- name    : Eden.diagonalLinear_comp_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:29:05.524523+00:00
-- url     : https://prove2.me/theorems/a65a4a41-1ed1-4480-87fa-91f92bb5f6b8
-- title:
--   Eden: diagonal Linear comp self
-- statement:
--   The Eden construction uses the diagonal Linear comp self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L29-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L29-L33

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.diagonalLinear_comp_self (d : PhaseSpace) :
    diagonalLinear d ∘ₗ diagonalLinear d =
      diagonalLinear (WithLp.toLp 2 (fun i => d i ^ 2)) := by sorry
