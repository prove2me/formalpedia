-- Prove2me | Theorems.Thm_FamousTheorems_banach_alaoglu
-- name    : FamousTheorems.banach_alaoglu
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T06:56:19.358399+00:00
-- url     : https://prove2.me/theorems/29070134-b750-4d66-9bb3-31c7d40de55d
-- title:
--   The Banach–Alaoglu theorem
-- statement:
--   **The Banach–Alaoglu theorem.**
--
--   If $s$ is a neighbourhood of the origin in a normed space $E$, then its polar
--   $$s^\circ = \{ f \in E^* : |f(x)| \le 1 \text{ for all } x \in s \}$$
--   is compact in the weak-* topology on the dual.
--
--   Taking $s$ to be the unit ball recovers the familiar form: the closed unit ball of $E^*$ is
--   weak-* compact. This is the standard repair for the failure of Heine–Borel in infinite
--   dimensions — by Riesz's lemma the dual unit ball is never norm-compact unless $E$ is
--   finite-dimensional, so one weakens the topology until compactness returns.
--
--   The proof is Tychonoff: the polar embeds as a closed subset of a product of discs
--   $\prod_{x \in s} \{|z| \le \lVert x\rVert\}$, which is compact.
--
--   Alaoglu proved it in 1940, with Banach having done the separable case earlier by a diagonal
--   argument. It underlies the existence of invariant measures, weak-* solutions in the calculus
--   of variations, and the Gelfand theory of commutative Banach algebras.
--
--   **Formalization note.** `WeakDual.polar 𝕜 s` is the polar viewed inside `WeakDual 𝕜 E`, the
--   dual carrying the weak-* topology, which is where the compactness lives; `ProperSpace 𝕜`
--   holds for $\mathbb{R}$ and $\mathbb{C}$. The result is Mathlib's `WeakDual.isCompact_polar`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open Filter Set Topology

theorem banach_alaoglu {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace 𝕜] {s : Set E}
    (s_nhds : s ∈ 𝓝 (0 : E)) : IsCompact (WeakDual.polar 𝕜 s) := by sorry

end FamousTheorems
