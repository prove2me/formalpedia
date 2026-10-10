-- Prove2me | Theorems.Thm_DirichletUnitTheorem_galois_nrRealPlaces_eq_zero_or_nrComplexPlaces_eq_zero
-- name    : DirichletUnitTheorem.galois_nrRealPlaces_eq_zero_or_nrComplexPlaces_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:02.012991+00:00
-- url     : https://prove2.me/theorems/600a3f03-fc1a-4322-92e6-28b68fc74fad
-- title:
--   Galois number fields: $r_1 = 0$ or $r_2 = 0$
-- statement:
--   Let $K$ be a number field that is Galois over $\mathbb Q$. Then either $r_1 = 0$ (all embeddings are non-real) or $r_2 = 0$ (all embeddings are real):
--
--   $$r_1 = 0 \quad\text{or}\quad r_2 = 0.$$
--
--   In other words a Galois number field is either totally real or totally complex.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section ("Note that if K is Galois over Q then either r1 = 0 or r2 = 0").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem galois_nrRealPlaces_eq_zero_or_nrComplexPlaces_eq_zero (K : Type*) [Field K]
    [NumberField K] [IsGalois ℚ K] :
    InfinitePlace.nrRealPlaces K = 0 ∨ InfinitePlace.nrComplexPlaces K = 0 := by sorry

end DirichletUnitTheorem
