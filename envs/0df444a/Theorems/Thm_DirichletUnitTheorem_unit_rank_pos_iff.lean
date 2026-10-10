-- Prove2me | Theorems.Thm_DirichletUnitTheorem_unit_rank_pos_iff
-- name    : DirichletUnitTheorem.unit_rank_pos_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:03.320566+00:00
-- url     : https://prove2.me/theorems/3cfc3784-f5d7-4b9b-a2b2-da08e43067e1
-- title:
--   The unit rank is positive except for $\mathbb Q$ and imaginary quadratic fields
-- statement:
--   Let $K$ be a number field. The unit rank of $K$ is positive if and only if $K$ is neither $\mathbb Q$ nor an imaginary quadratic field:
--
--   $$\operatorname{rank}\mathcal O_K^\times > 0 \iff \neg\big([K:\mathbb Q]=1 \ \text{ or }\ ([K:\mathbb Q]=2 \text{ and } K \text{ imaginary})\big).$$
--
--   Equivalently, $\mathbb Q$ and the imaginary quadratic fields are exactly the number fields with only finitely many units.
--
--   **Formalization Note** "$K$ is $\mathbb Q$" is encoded as $[K:\mathbb Q]=1$; "imaginary quadratic" as degree $2$ and `IsTotallyComplex`.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section ("The rank is positive for all number fields besides Q and imaginary quadratic fields, which have rank 0").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem unit_rank_pos_iff (K : Type*) [Field K] [NumberField K] :
    0 < Module.rank ℤ (Additive (𝓞 K)ˣ) ↔
      ¬ (Module.finrank ℚ K = 1 ∨ (Module.finrank ℚ K = 2 ∧ IsTotallyComplex K)) := by sorry

end DirichletUnitTheorem
