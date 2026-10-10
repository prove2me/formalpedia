-- Prove2me | Theorems.Thm_DirichletUnitTheorem_dirichlet_unit_theorem
-- name    : DirichletUnitTheorem.dirichlet_unit_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:28.698587+00:00
-- url     : https://prove2.me/theorems/00d0667d-6fdc-48c4-83e7-39299f9c8508
-- title:
--   Dirichlet's unit theorem
-- statement:
--   **Dirichlet's unit theorem.** Let $K$ be a number field with ring of integers $\mathcal O_K$, let $r_1$ be the number of real embeddings of $K$ and $r_2$ the number of conjugate pairs of complex (non-real) embeddings of $K$. Then the unit group $\mathcal O_K^\times$ is finitely generated, and its rank (the maximal number of multiplicatively independent units) is
--
--   $$\operatorname{rank}\,\mathcal O_K^\times = r_1 + r_2 - 1.$$
--
--   Together with the finiteness of the torsion subgroup this means $\mathcal O_K^\times \cong \mu(K)\times\mathbb Z^{r_1+r_2-1}$, where $\mu(K)$ is the finite cyclic group of roots of unity in $K$. It is one of the two basic finiteness theorems of algebraic number theory, alongside finiteness of the class group.
--
--   **Formalization Note** The rank is Mathlib's `Module.rank ℤ` of the additive version of the unit group, a cardinal; $r_1$ and $r_2$ are Mathlib's `nrRealPlaces` and `nrComplexPlaces`. The natural-number subtraction is harmless because $r_1+r_2\ge 1$.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section ("The statement is that the group of units is finitely generated and has rank ... r = r1 + r2 − 1").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem dirichlet_unit_theorem (K : Type*) [Field K] [NumberField K] :
    Group.FG (𝓞 K)ˣ ∧
      Module.rank ℤ (Additive (𝓞 K)ˣ) =
        ((InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 : ℕ) : Cardinal) := by sorry

end DirichletUnitTheorem
