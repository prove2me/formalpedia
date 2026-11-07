-- Prove2me | Theorems.Thm_ClawFreeChoosable_lemma_7_4_minimum_counterexamples
-- name    : ClawFreeChoosable.lemma_7_4_minimum_counterexamples
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:54.16466+00:00
-- url     : https://prove2.me/theorems/770056da-1b9c-4327-b59b-0b585288749f
-- title:
--   Lemma 7.4 — minimum counterexamples
-- statement:
--   Fix a nonnegative integer $k$ and a class $\mathcal C$ of finite graphs closed under taking induced subgraphs. Let $(G, S, \phi, L)$ be an uncolourable (Pk)-instance with $G \in \mathcal C$ and $\omega(G) \le k$, and suppose $|V(G)|$ is minimum among all uncolourable (Pk)-instances $(H, T, \psi, M)$ with $H \in \mathcal C$ and $\omega(H) \le k$ (over all finite vertex sets and all colour sets). Then
--
--   1. $G$ is connected;
--   2. every simplicial vertex of $G$ belongs to $S$;
--   3. every proper induced subgraph $G[X]$, $X \ne V(G)$, satisfies (Pk).
--
--   This is the minimum-counterexample framework in which Theorems 10.5, 11.10 and 1.3 are proved.
--
--   Differences from the source:
--   - generalization: a class C of graphs closed under induced subgraphs → a predicate 𝒞 W H on graphs H : SimpleGraph W, with 𝒞 W H → 𝒞 X (H.induce X) for every X ⊆ W, not required to be closed under isomorphism; reason: every class of graphs in the source's sense (closed under induced subgraphs, and under isomorphism if one reads it so) is such a predicate, so the Lean statement specializes to the source's; the proof only passes to induced subgraphs
--   - encoding: choose an uncolorable (Pk)-instance with |V(G)| minimum → the hypothesis that every uncolorable (Pk)-instance on a graph of 𝒞 with clique number ≤ k, on any finite vertex type and with any colour type, has at least |V(G)| vertices; reason: this is what minimality means; same instances
--   - encoding: G is connected → Mathlib's Connected, which includes nonemptiness; reason: an uncolourable instance has a nonempty graph (the empty graph is colourable), so connectivity in the source's sense is the same
--   - encoding: proper induced subgraph → G.induce X with X ≠ V; reason: Lean convention; same instances
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Lemma 7.4, p.10 (PDF p.13)

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsSimplicialClique
import Definitions.Def_ClawFreeChoosable_SatisfiesP

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Lemma 7.4 (Minimum counterexamples)** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.10). Fix a nonnegative integer `k` and a
class `𝒞` closed under induced subgraphs. Among all uncolorable (Pk)-instances `(G, S, ϕ, L)`
with `G ∈ 𝒞` and `ω(G) ≤ k`, choose one with `|V(G)|` minimum. Then `G` is connected, every
simplicial vertex of `G` belongs to `S`, and every proper induced subgraph of `G` satisfies (Pk).

**Formalization Note.** The class is a predicate `𝒞 W H` on graphs `H : SimpleGraph W`, closed
under taking induced subgraphs `H.induce X`. Minimality ranges over every uncolorable
(Pk)-instance, over any finite vertex type and any colour type, on a graph of `𝒞` with clique
number at most `k`. A proper induced subgraph is `G.induce X` with `X ≠ V(G)`. Mathlib's
`Connected` includes nonemptiness (a minimum counterexample is nonempty). -/
theorem lemma_7_4_minimum_counterexamples (k : ℕ) (𝒞 : ∀ W : Type, SimpleGraph W → Prop)
    (h𝒞 : ∀ (W : Type) (H : SimpleGraph W) (X : Set W), 𝒞 W H → 𝒞 X (H.induce X))
    {V : Type} [Fintype V] (G : SimpleGraph V) {α : Type} (S : Set V) (ϕ : V → α)
    (L : V → Finset α) (hG : 𝒞 V G) (hω : G.cliqueNum ≤ k) (hinst : IsPInstance G k S ϕ L)
    (hunc : ¬ PColorable G S ϕ L)
    (hmin : ∀ (W : Type) [Fintype W] (H : SimpleGraph W) (β : Type) (T : Set W) (ψ : W → β)
      (M : W → Finset β), 𝒞 W H → H.cliqueNum ≤ k → IsPInstance H k T ψ M →
        ¬ PColorable H T ψ M → Fintype.card V ≤ Fintype.card W) :
    G.Connected ∧ (∀ v : V, IsSimplicial G v → v ∈ S) ∧
      ∀ X : Set V, X ≠ Set.univ → SatisfiesP (G.induce X) k := by sorry

end ClawFreeChoosable
