-- Prove2me | Theorems.Thm_DirichletUnitTheorem_dirichlet_unit_theorem_order
-- name    : DirichletUnitTheorem.dirichlet_unit_theorem_order
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:20.473913+00:00
-- url     : https://prove2.me/theorems/4bef2063-3761-43ac-b2af-1fc60ea5005a
-- title:
--   Dirichlet's unit theorem for orders
-- statement:
--   Let $K$ be a number field and let $\mathcal O\subseteq\mathcal O_K$ be an order, i.e. a subring of $\mathcal O_K$ of finite index (as an additive subgroup). Then $\mathcal O^\times$ is finitely generated of rank
--
--   $$\operatorname{rank}\mathcal O^\times = r_1 + r_2 - 1.$$
--
--   So the unit theorem applies not only to the maximal order $\mathcal O_K$ but to every order.
--
--   **Formalization Note** An order is encoded as a subring of $\mathcal O_K$ whose additive group has finite index; every order of $K$ is of this form.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section ("The theorem not only applies to the maximal order OK but to any order O ⊂ OK").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem dirichlet_unit_theorem_order (K : Type*) [Field K] [NumberField K]
    (O : Subring (𝓞 K)) (hO : O.toAddSubgroup.FiniteIndex) :
    Group.FG Oˣ ∧
      Module.rank ℤ (Additive Oˣ) =
        ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : Cardinal) := by sorry

end DirichletUnitTheorem
