-- Prove2me | Theorems.Thm_DirichletUnitTheorem_degree_eq_nrRealPlaces_add_two_mul_nrComplexPlaces
-- name    : DirichletUnitTheorem.degree_eq_nrRealPlaces_add_two_mul_nrComplexPlaces
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:50.00214+00:00
-- url     : https://prove2.me/theorems/45bc73be-4c5a-49df-bd90-e7d723468c50
-- title:
--   $n = r_1 + 2r_2$
-- statement:
--   Let $K$ be a number field of degree $n=[K:\mathbb Q]$, with $r_1$ real embeddings and $r_2$ conjugate pairs of non-real complex embeddings. Then
--
--   $$n = r_1 + 2r_2.$$
--
--   This is the counting identity behind the definition of $r_1$ and $r_2$: the $n$ embeddings $K\to\mathbb C$ are either real or come in complex-conjugate pairs.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section, identity n = r1 + 2r2.

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem degree_eq_nrRealPlaces_add_two_mul_nrComplexPlaces (K : Type*) [Field K]
    [NumberField K] :
    InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K := by sorry

end DirichletUnitTheorem
