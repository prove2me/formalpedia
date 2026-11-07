-- Prove2me | Theorems.Thm_ClawFreeChoosable_lemma_12_1_double_clique_sums
-- name    : ClawFreeChoosable.lemma_12_1_double_clique_sums
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:13.605793+00:00
-- url     : https://prove2.me/theorems/4ed0fe62-4654-4242-8c2d-6a793565a5d4
-- title:
--   Lemma 12.1 — double clique sums preserve (Pk)
-- statement:
--   Let $(V_1, C_1, C_2, V_2)$ be a double clique cutset of a finite graph $G$, so that $G$ is the double clique-sum of $G_1 = G[V_1 \cup D]$ and $G_2 = G[V_2 \cup D]$ with $D = C_1 \cup C_2$, and let $k \ge \omega(G)$ be an integer. If both $G_1$ and $G_2$ satisfy (Pk), then $G$ satisfies (Pk).
--
--   The lemma lets a minimum counterexample to (Pk) be assumed to have no double clique cutset.
--
--   Differences from the source:
--   - encoding: G is the double clique-sum of G1 = G[V1 ∪ D] and G2 = G[V2 ∪ D], D = C1 ∪ C2 → IsDoubleCliqueCutset G V₁ C₁ C₂ V₂, with G₁, G₂ the induced subgraphs on V₁ ∪ C₁ ∪ C₂ and V₂ ∪ C₁ ∪ C₂; reason: this is the definition of a double clique-sum (§12.1, p.32); same instances
--   - encoding: (Pk)/(Mk) are defined for an integer k ≥ ω(G) → k : ℕ with the hypothesis cliqueNum ≤ k, the property itself not bundling it; reason: Lean convention; same instances
--   - generalization: a double clique cutset is a clique cutset, i.e. a clique whose deletion disconnects a connected graph (§1, p.1), so G is connected → no connectivity hypothesis on G; reason: every connected G is an instance, so the Lean statement specializes to the source's; the proof (p.32) never uses connectivity
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Lemma 12.1, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_ClawFreeChoosable_HasDoubleCliqueCutset
import Definitions.Def_ClawFreeChoosable_SatisfiesP

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Lemma 12.1 (Double clique sums)** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.32). Let `G` be the double clique-sum of
`G₁ = G[V₁ ∪ D]` and `G₂ = G[V₂ ∪ D]`, where `D = C₁ ∪ C₂` (disjoint), and let `k ≥ ω(G)`. If
both `G₁` and `G₂` satisfy (Pk), then `G` satisfies (Pk).

**Formalization Note.** "`G` is the double clique-sum of `G[V₁ ∪ D]` and `G[V₂ ∪ D]`" is the
hypothesis that `(V₁, C₁, C₂, V₂)` is a double clique cutset of `G` (§12.1, p.32); the pieces
are the induced subgraphs `G.induce (V₁ ∪ C₁ ∪ C₂)` and `G.induce (V₂ ∪ C₁ ∪ C₂)`. -/
theorem lemma_12_1_double_clique_sums {V : Type} [Fintype V] (G : SimpleGraph V)
    (V₁ C₁ C₂ V₂ : Set V) (hD : IsDoubleCliqueCutset G V₁ C₁ C₂ V₂) (k : ℕ)
    (hk : G.cliqueNum ≤ k) (h₁ : SatisfiesP (G.induce (V₁ ∪ C₁ ∪ C₂)) k)
    (h₂ : SatisfiesP (G.induce (V₂ ∪ C₁ ∪ C₂)) k) : SatisfiesP G k := by sorry

end ClawFreeChoosable
