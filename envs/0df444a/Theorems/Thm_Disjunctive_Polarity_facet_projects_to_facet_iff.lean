-- Prove2me | Theorems.Thm_Disjunctive_Polarity_facet_projects_to_facet_iff
-- name    : Disjunctive.Polarity.facet_projects_to_facet_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:18:25.378781+00:00
-- url     : https://prove2.me/theorems/8c70fa44-d98d-4567-b80d-423d2dde5cc4
-- title:
--   Corollary 2.9 — when a facet's projection is a facet
-- statement:
--   This is Corollary 2.9 of Balas's *Disjunctive Programming*: exactly when does a facet of $Q$
--   project to a facet of $\mathrm{Proj}_x(Q)$, rather than to a lower-dimensional or non-face subset?
--
--   $$
--   \mathrm{Proj}_x(F_Q) \text{ is a facet of } \mathrm{Proj}_x(Q) \iff r_F^* = r^*.
--   $$
--
--   The projection of a face need not be a face in general (the top vertex of a pyramid projects to
--   an interior point of its base, not a face of the base), so this is a genuine structural fact, not
--   merely a dimension count: when $r_F^* = r^*$, the facet's defining inequality descends to a valid
--   inequality for $\mathrm{Proj}_x(Q)$ itself, which is what makes the projection a face.
--
--   **Formalization Note.** `IsFacet` bundles both requirements (being an extreme subset, i.e. a
--   face, and having codimension exactly $1$), so the displayed equivalence is between two genuine
--   facet conditions, not two dimension equalities.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 30, Corollary 2.9

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_EqualitySubsystem

namespace Disjunctive.Polarity

/-- Corollary 2.9 (Balas §2.2.3, p. 30): the projection of a facet `FQ` of `Q` is itself a facet
of `Proj_x(Q)` if and only if `FQ`'s and `Q`'s equality-subsystem `u`-ranks agree. -/
theorem facet_projects_to_facet_iff {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ)
    (hFacet : IsFacet (Poly2 A B b) (FacetCandidate A B b α β β0)) :
    IsFacet (ProjOntoX (Poly2 A B b)) (ProjOntoX (FacetCandidate A B b α β β0)) ↔
      SystemRankA (Fin.cons α A)
          (TightRows (Fin.cons α A) (Fin.cons β B) (Fin.cons β0 b)
            (FacetCandidate A B b α β β0)) =
        EqRankA A B b := by sorry

end Disjunctive.Polarity
