-- Prove2me | Theorems.Thm_Disjunctive_Polarity_facet_projection_dimension
-- name    : Disjunctive.Polarity.facet_projection_dimension
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:17:50.540808+00:00
-- url     : https://prove2.me/theorems/9d84c797-1f10-4b24-a89b-e0d1bc4b3050
-- title:
--   Corollary 2.8 — dimension of the projection of a facet
-- statement:
--   This is Corollary 2.8 of Balas's *Disjunctive Programming*, applying Theorem 2.7 to a facet
--   $F_Q$ of $Q$ cut out by a valid inequality $\alpha u + \beta x \le \beta_0$.
--
--   $$
--   \dim(\mathrm{Proj}_x(F_Q)) = \dim(\mathrm{Proj}_x(Q)) - 1 + (r_F^* - r^*),
--   $$
--
--   where $r_F^*$ is the rank of the $u$-columns of $F_Q$'s own equality subsystem (the original
--   system's tight rows together with the facet's defining inequality). The difference $r_F^* - r^*$
--   measures how many fewer dimensions are "lost" projecting the facet than projecting $Q$ itself.
--
--   **Formalization Note.** $r_F^*$ is computed via `SystemRankA` applied to the row-augmented system
--   `Fin.cons α A`, `Fin.cons β B`, `Fin.cons β0 b` (appending the facet's defining inequality as one
--   extra row), restricted to the rows tight throughout the facet.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 30, Corollary 2.8

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Corollary 2.8 (Balas §2.2.3, p. 30): the dimension of the projection of a facet `FQ` of `Q`,
in terms of the dimension of `Proj_x(Q)` and the ranks `r*_F`, `r*` of the `u`-columns of `FQ`'s
and `Q`'s own equality subsystems. -/
theorem facet_projection_dimension {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ)
    (hFacet : IsFacet (Poly2 A B b) (FacetCandidate A B b α β β0)) :
    PolyDim (ProjOntoX (FacetCandidate A B b α β β0)) =
      PolyDim (ProjOntoX (Poly2 A B b)) - 1 +
        ((SystemRankA (Fin.cons α A)
            (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
              (FacetCandidate A B b α β β0)) : ℤ) -
          (EqRankA A B b : ℤ)) := by sorry

end Disjunctive.Polarity
