-- Prove2me | Theorems.Thm_FamousTheorems_jones_lemma_not_normal_6b
-- name    : FamousTheorems.jones_lemma_not_normal_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:00.076503+00:00
-- url     : https://prove2.me/theorems/aa4046b1-97d0-4ba6-aba1-f73678ba4531
-- title:
--   Jones's lemma on non-normal spaces
-- statement:
--   **Jones's lemma on non-normal spaces.** Let $X$ be a separable topological space containing a closed discrete subset $s$ with $|s|\ge\mathfrak c=2^{\aleph_0}$. Then $X$ is not normal.
--
--   In a normal space, disjoint closed sets can be separated by open sets. Jones's lemma (1937) shows that a separable normal space cannot contain a closed discrete set as large as the continuum. It gives a quick proof that the Sorgenfrey plane and the Niemytzki (Moore) plane are not normal, and hence that normality is not preserved by products.
--
--   **Formalization note.** Mathlib's `IsClosed.not_normal_of_continuum_le_mk`. `DiscreteTopology s` says that the subspace topology on $s$ is discrete, and `Cardinal.continuum` is $\mathfrak c$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsClosed.not_normal_of_continuum_le_mk`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jones_lemma_not_normal_6b {X : Type*} [TopologicalSpace X] [TopologicalSpace.SeparableSpace X] {s : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hc : Cardinal.continuum ≤ Cardinal.mk s) : ¬NormalSpace X := by sorry

end FamousTheorems
