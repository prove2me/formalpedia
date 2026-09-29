-- Prove2me | Theorems.Thm_FamousTheorems_archimedean_subgroup_dense_or_cyclic_7a
-- name    : FamousTheorems.archimedean_subgroup_dense_or_cyclic_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:03.369703+00:00
-- url     : https://prove2.me/theorems/17a25d40-cb35-43e5-afe2-5cf9ee84396e
-- title:
--   A subgroup of an archimedean ordered group is dense or cyclic
-- statement:
--   **A subgroup of an archimedean ordered group is dense or cyclic.** Let $G$ be a linearly ordered commutative group with the order topology that is archimedean. Every subgroup $S$ of $G$ is either dense in $G$ or cyclic, $S=\langle a\rangle$ for some $a\in G$.
--
--   For $G=\mathbb R$ this is the classical dichotomy for additive subgroups of the reals. It implies that $a\mathbb Z+b\mathbb Z$ is dense when $a/b$ is irrational, and hence Kronecker's density theorem for irrational rotations. It is also used for the classification of closed subgroups of $\mathbb R$ and of the circle.
--
--   **Formalization note.** Mathlib's `Subgroup.dense_or_cyclic`. The group is written multiplicatively. `MulArchimedean G` says that for every $x$ and every $y>1$ some power $y^n$ exceeds $x$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subgroup.dense_or_cyclic`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem archimedean_subgroup_dense_or_cyclic_7a {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [TopologicalSpace G] [OrderTopology G]
    [MulArchimedean G] (S : Subgroup G) : Dense (S : Set G) ∨ ∃ a : G, S = Subgroup.closure {a} := by sorry

end FamousTheorems
