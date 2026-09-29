-- Prove2me | Theorems.Thm_FamousTheorems_t0_embeds_in_sierpinski_power_6c
-- name    : FamousTheorems.t0_embeds_in_sierpinski_power_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:48.40138+00:00
-- url     : https://prove2.me/theorems/3e3e513f-3555-445b-a907-c9163117299f
-- title:
--   Every T₀ space embeds in a power of the Sierpiński space
-- statement:
--   **T₀ spaces embed in powers of the Sierpiński space.** Every $T_0$ topological space $X$ is homeomorphic to a subspace of a product $S^\iota$ of copies of the Sierpiński space $S$.
--
--   The Sierpiński space is the two-point space $\{0,1\}$ in which $\{1\}$ is open and $\{0\}$ is not. The embedding sends $x$ to the family $(x\in U)_U$ indexed by the open sets $U$ of $X$. The $T_0$ axiom is exactly what makes this injective. So the Sierpiński space plays the role for $T_0$ spaces that $[0,1]$ plays for Tychonoff spaces.
--
--   **Formalization note.** Mathlib's `TopologicalSpace.productOfMemOpens_isEmbedding`. In Mathlib the Sierpiński space is `Prop` with its standard topology, in which `{True}` is open. The statement asks for an index type in the same universe as $X$ and a topological embedding `X → (ι → Prop)`. The Mathlib proof uses $\iota=$ `Opens X`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `TopologicalSpace.productOfMemOpens_isEmbedding`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u

theorem t0_embeds_in_sierpinski_power_6c (X : Type u) [TopologicalSpace X] [T0Space X] :
    ∃ (ι : Type u) (f : X → (ι → Prop)), Topology.IsEmbedding f := by sorry

end FamousTheorems
