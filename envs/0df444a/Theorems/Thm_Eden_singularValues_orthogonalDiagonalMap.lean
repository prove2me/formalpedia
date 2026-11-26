-- Prove2me | Theorems.Thm_Eden_singularValues_orthogonalDiagonalMap
-- name    : Eden.singularValues_orthogonalDiagonalMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:36.658688+00:00
-- url     : https://prove2.me/theorems/716764a4-ac0d-5a70-87c4-eff1db76bb69
-- title:
--   Eden: singular Values orthogonal Diagonal Map
-- statement:
--   The five singular values, with multiplicities, are the nonnegative diagonal
--   entries of an orthogonal factorisation. No ordering of those entries is assumed.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L75-L89
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L75-L89

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.singularValues_orthogonalDiagonalMap
    (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) (hd : ∀ i, 0 ≤ d i) :
    Finset.univ.val.map (fun i : Fin 5 => (orthogonalDiagonalMap U V d).singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => d i) := by sorry
