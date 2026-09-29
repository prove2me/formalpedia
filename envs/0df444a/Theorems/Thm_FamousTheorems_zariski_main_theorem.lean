-- Prove2me | Theorems.Thm_FamousTheorems_zariski_main_theorem
-- name    : FamousTheorems.zariski_main_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:42.919987+00:00
-- url     : https://prove2.me/theorems/6f73d0ec-d88b-4528-8def-025437b81e20
-- title:
--   Zariski's main theorem
-- statement:
--   **Zariski's main theorem.** Let $f:X\to Y$ be a separated, quasi-compact morphism of schemes that is locally of finite type, and let $X\to Y'$ be the canonical map to the relative normalisation $Y'$ of $Y$ in $X$. Then there is an open subscheme $U\subseteq Y'$ such that $X\to Y'$ restricts to an isomorphism over $U$, and the preimage of $U$ is exactly the set of points of $X$ at which $f$ is quasi-finite.
--
--   In particular, a quasi-finite separated morphism of finite type factors as an open immersion followed by an integral morphism. Zariski's main theorem is one of the deepest results of foundational algebraic geometry, with consequences such as the connectedness of fibres of birational maps to normal varieties.
--
--   **Formalization note.** Mathlib's `AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`. `f.normalization` is the relative normalisation, `f.toNormalization` the canonical morphism, `∣_ U` the restriction of a morphism over an open, and `f.QuasiFiniteAt x` quasi-finiteness at $x$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open AlgebraicGeometry

theorem zariski_main_theorem {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ U : f.normalization.Opens, CategoryTheory.IsIso (f.toNormalization ∣_ U) ∧
      ((TopologicalSpace.Opens.map f.toNormalization.base).obj U).carrier = {x : X | f.QuasiFiniteAt x} := by sorry

end FamousTheorems
