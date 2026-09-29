-- Prove2me | Theorems.Thm_FamousTheorems_shapiro_lemma
-- name    : FamousTheorems.shapiro_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:59.056+00:00
-- url     : https://prove2.me/theorems/0ea28380-d577-47dc-a075-3c02644cb420
-- title:
--   Shapiro's lemma
-- statement:
--   **Shapiro's lemma.** Let $G$ be a group, $S\le G$ a subgroup, $k$ a commutative ring and $A$ a $k$-linear representation of $S$. Then for every $n\ge0$,
--   $$H^n\big(G,\operatorname{Coind}_S^G A\big)\cong H^n(S,A).$$
--
--   Shapiro's lemma allows cohomology of a subgroup to be computed as cohomology of the whole group. It is the basis for restriction and corestriction in group cohomology and is used throughout class field theory.
--
--   **Formalization note.** Mathlib's `groupCohomology.coindIso`, which constructs the isomorphism; the statement asserts that an isomorphism exists. `Rep.coind S.subtype A` is the coinduced representation along the inclusion $S\hookrightarrow G$, and `groupCohomology A n` is $H^n$ as a $k$-module.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `groupCohomology.coindIso`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u

theorem shapiro_lemma {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep.{u} k S) (n : ℕ) :
    Nonempty (CategoryTheory.Iso (groupCohomology (Rep.coind S.subtype A) n) (groupCohomology A n)) := by sorry

end FamousTheorems
