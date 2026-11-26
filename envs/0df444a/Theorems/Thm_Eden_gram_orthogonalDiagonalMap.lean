-- Prove2me | Theorems.Thm_Eden_gram_orthogonalDiagonalMap
-- name    : Eden.gram_orthogonalDiagonalMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:30.811261+00:00
-- url     : https://prove2.me/theorems/8f1f8d1d-d7de-4aae-927b-bbbda3773bec
-- title:
--   Eden: gram orthogonal Diagonal Map
-- statement:
--   The Eden construction uses the gram orthogonal Diagonal Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L59-L65
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L59-L65

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.gram_orthogonalDiagonalMap (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) :
    (orthogonalDiagonalMap U V d).adjoint ∘ₗ orthogonalDiagonalMap U V d =
      V.toLinearEquiv.conj (diagonalLinear (WithLp.toLp 2 (fun i => d i ^ 2))) := by sorry
