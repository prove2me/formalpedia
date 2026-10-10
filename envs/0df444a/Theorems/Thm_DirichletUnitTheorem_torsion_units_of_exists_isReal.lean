-- Prove2me | Theorems.Thm_DirichletUnitTheorem_torsion_units_of_exists_isReal
-- name    : DirichletUnitTheorem.torsion_units_of_exists_isReal
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:45.010909+00:00
-- url     : https://prove2.me/theorems/d4c7dbfd-a1e8-4288-bb33-2c49b1df4d40
-- title:
--   With a real embedding, the torsion units are $\pm1$
-- statement:
--   Let $K$ be a number field with at least one real embedding. Then the only units of $\mathcal O_K$ of finite order are $\pm1$:
--
--   $$u\in\mathcal O_K^\times,\ u^n=1 \text{ for some } n\ge1 \ \Longrightarrow\ u=1 \text{ or } u=-1.$$
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section ("For a number field with at least one real embedding the torsion must therefore be only {1,−1}").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem torsion_units_of_exists_isReal (K : Type*) [Field K] [NumberField K]
    (h : ∃ w : InfinitePlace K, w.IsReal) (u : (𝓞 K)ˣ) (hu : IsOfFinOrder u) :
    u = 1 ∨ u = -1 := by sorry

end DirichletUnitTheorem
