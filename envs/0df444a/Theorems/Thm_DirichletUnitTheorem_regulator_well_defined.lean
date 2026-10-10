-- Prove2me | Theorems.Thm_DirichletUnitTheorem_regulator_well_defined
-- name    : DirichletUnitTheorem.regulator_well_defined
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:20.264402+00:00
-- url     : https://prove2.me/theorems/41bf8ccf-db03-48cb-ac34-978d700da51b
-- title:
--   The regulator is independent of the generators and of the deleted column, and positive
-- statement:
--   Let $K$ be a number field, $r=r_1+r_2-1$, and let $u_1,\dots,u_r$ and $v_1,\dots,v_r$ be two systems of generators of $\mathcal O_K^\times$ modulo roots of unity. Form the $r\times(r+1)$ matrices $\big(N_j\log\lvert\sigma_j(u_i)\rvert\big)$ and $\big(N_j\log\lvert\sigma_j(v_i)\rvert\big)$, columns indexed by the infinite places. Delete any one column from the first and any one column from the second. Then the two square submatrices have determinants of the same absolute value $R$, and $R>0$.
--
--   This common value $R$ is the **regulator** of $K$; the statement says it does not depend on the choice of generators nor on the deleted column, and is a positive real number.
--
--   **Formalization Note** Deleting the column of place $w_1$ leaves a square matrix whose rows and columns are both indexed by the places $\neq w_1$, the rows being matched to $u_1,\dots,u_r$ through an arbitrary bijection $e_1$; reordering rows only changes the sign of the determinant.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), section "The regulator" ("the absolute value R of the determinant of the submatrix formed by deleting one column is independent of the column ... it does not depend on the choice of generators ui"; lead: "The regulator is a positive real number").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem regulator_well_defined (K : Type*) [Field K] [NumberField K]
    [DecidableEq (InfinitePlace K)]
    (u v : Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) → (𝓞 K)ˣ)
    (hu : ∀ x : (𝓞 K)ˣ, ∃ ζ : (𝓞 K)ˣ, IsOfFinOrder ζ ∧ ∃ n : Fin _ → ℤ, x = ζ * ∏ i, u i ^ n i)
    (hv : ∀ x : (𝓞 K)ˣ, ∃ ζ : (𝓞 K)ˣ, IsOfFinOrder ζ ∧ ∃ n : Fin _ → ℤ, x = ζ * ∏ i, v i ^ n i)
    (w₁ w₂ : InfinitePlace K)
    (e₁ : {w // w ≠ w₁} ≃ Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1))
    (e₂ : {w // w ≠ w₂} ≃ Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1)) :
    |(Matrix.of fun (i j : {w // w ≠ w₁}) =>
        ((j : InfinitePlace K).mult : ℝ) * Real.log ((j : InfinitePlace K) ((u (e₁ i) : 𝓞 K) : K))).det| =
      |(Matrix.of fun (i j : {w // w ≠ w₂}) =>
        ((j : InfinitePlace K).mult : ℝ) * Real.log ((j : InfinitePlace K) ((v (e₂ i) : 𝓞 K) : K))).det| ∧
    0 < |(Matrix.of fun (i j : {w // w ≠ w₁}) =>
        ((j : InfinitePlace K).mult : ℝ) * Real.log ((j : InfinitePlace K) ((u (e₁ i) : 𝓞 K) : K))).det| := by sorry

end DirichletUnitTheorem
