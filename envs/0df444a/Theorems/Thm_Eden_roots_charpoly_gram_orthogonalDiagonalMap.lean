-- Prove2me | Theorems.Thm_Eden_roots_charpoly_gram_orthogonalDiagonalMap
-- name    : Eden.roots_charpoly_gram_orthogonalDiagonalMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:32.804392+00:00
-- url     : https://prove2.me/theorems/ccbd8da7-de77-510b-8659-d3ea04a913ae
-- title:
--   Eden: roots charpoly gram orthogonal Diagonal Map
-- statement:
--   The Eden construction uses the roots charpoly gram orthogonal Diagonal Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L67-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L67-L71

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.roots_charpoly_gram_orthogonalDiagonalMap
    (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) :
    ((orthogonalDiagonalMap U V d).adjoint ∘ₗ orthogonalDiagonalMap U V d).charpoly.roots =
      Finset.univ.val.map (fun i : Fin 5 => d i ^ 2) := by sorry
