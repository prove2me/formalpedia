-- Prove2me | Theorems.Thm_FamousTheorems_grassmann_dimension_formula_7b
-- name    : FamousTheorems.grassmann_dimension_formula_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:32.720158+00:00
-- url     : https://prove2.me/theorems/9a6452c9-6166-4d8d-bb09-e1a59be671c9
-- title:
--   Grassmann's dimension formula dim(U+W)+dim(U∩W)=dim U+dim W
-- statement:
--   **Grassmann's dimension formula.** Let $U$ and $W$ be finite-dimensional subspaces of a vector space $V$ over a division ring. Then
--   $$\dim(U+W)+\dim(U\cap W)=\dim U+\dim W.$$
--
--   This is the linear algebra version of the inclusion–exclusion principle. It implies, for example, that two planes through the origin in $\mathbb R^3$ meet in at least a line, and more generally that subspaces of large enough dimension must intersect. It follows from the rank–nullity theorem applied to the map $U\times W\to U+W$, $(u,w)\mapsto u+w$, whose kernel is isomorphic to $U\cap W$.
--
--   **Formalization note.** Mathlib's `Submodule.finrank_sup_add_finrank_inf_eq`. `U ⊔ W` is the sum of subspaces and `U ⊓ W` their intersection. `Module.finrank` is the dimension.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Submodule.finrank_sup_add_finrank_inf_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem grassmann_dimension_formula_7b {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] (U W : Submodule K V)
    [FiniteDimensional K U] [FiniteDimensional K W] :
    Module.finrank K ↥(U ⊔ W) + Module.finrank K ↥(U ⊓ W) = Module.finrank K U + Module.finrank K W := by sorry

end FamousTheorems
