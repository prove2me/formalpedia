-- Prove2me | Theorems.Thm_DirichletUnitTheorem_nrPlaces_eq_card_roots_minpoly
-- name    : DirichletUnitTheorem.nrPlaces_eq_card_roots_minpoly
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:14.905395+00:00
-- url     : https://prove2.me/theorems/5f82746f-bff9-4224-a96d-2e5f2c20cadb
-- title:
--   $r_1$, $2r_2$ via roots of the minimal polynomial of a primitive element
-- statement:
--   Let $K$ be a number field and let $\alpha\in K$ be a primitive element, $K=\mathbb Q(\alpha)$, with minimal polynomial $f\in\mathbb Q[x]$. Then
--
--   1. $r_1$ is the number of real roots of $f$, and
--   2. $2r_2$ is the number of non-real complex roots of $f$.
--
--   This gives a practical way to compute the signature $(r_1,r_2)$ of $K$.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section, first bullet of "Other ways of determining r1 and r2".

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem nrPlaces_eq_card_roots_minpoly (K : Type*) [Field K] [NumberField K] (α : K)
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) :
    InfinitePlace.nrRealPlaces K = ((minpoly ℚ α).rootSet ℝ).ncard ∧
      2 * InfinitePlace.nrComplexPlaces K =
        {z : ℂ | z ∈ (minpoly ℚ α).rootSet ℂ ∧ z.im ≠ 0}.ncard := by sorry

end DirichletUnitTheorem
