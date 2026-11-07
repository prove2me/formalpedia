-- Prove2me | Theorems.Thm_ClawFreeChoosable_lemma_7_3_simplicial_cliques
-- name    : ClawFreeChoosable.lemma_7_3_simplicial_cliques
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:40.385902+00:00
-- url     : https://prove2.me/theorems/4c718fb6-63b8-416d-8cbd-b5592d51e86f
-- title:
--   Lemma 7.3 — simplicial cliques
-- statement:
--   Let $S$ be a clique of simplicial vertices in a finite graph $G$ and put $Q = N_G(S)$, the external neighbourhood of $S$. Then
--
--   1. the vertices of $S$ are pairwise true twins, and $S \cup Q$ is a clique;
--   2. if $G$ is claw-free, then (a) $Q$ is an attachable clique of $G - S$, and (b) for every integer $k \ge \omega(G)$ and every (Pk)-instance $(G, S, \phi, L)$, with the lists on $G - S$
--   $$L'(v) = \begin{cases} L(v) \setminus \phi(S), & v \in Q,\\ L(v), & v \notin S \cup Q,\end{cases}$$
--   the tuple $(G - S, Q, |S|, L')$ is an (Mk)-instance, and $G - S$ has a proper $L'$-colouring if and only if $(G, S, \phi, L)$ is colourable.
--
--   The lemma converts precolouring extension on $G$ into a mixed-list colouring problem on $G - S$; it is the bridge between (Pk) and (Mk) used throughout the proof of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: G − S, with Q and L′ as objects of G − S → G.induce Sᶜ on the subtype of vertices outside S; Q and L′ are read through the underlying vertex; reason: Lean convention; same instances
--   - encoding: (Pk)/(Mk) are defined for an integer k ≥ ω(G) → k : ℕ with the hypothesis cliqueNum ≤ k, the property itself not bundling it; reason: Lean convention; same instances
--   - encoding: ϕ a colouring of G[S], L a list assignment on V(G) \ S, colours unspecified → ϕ : V → α and L : V → Finset α over an arbitrary colour type α, only ϕ on S and L off S read; reason: Lean convention; same instances
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Lemma 7.3, p.10 (PDF p.13)

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_ClawFreeChoosable_IsClawFree
import Definitions.Def_ClawFreeChoosable_IsSimplicialClique
import Definitions.Def_ClawFreeChoosable_TrueTwins
import Definitions.Def_ClawFreeChoosable_extNbhd
import Definitions.Def_ClawFreeChoosable_IsAttachable
import Definitions.Def_ClawFreeChoosable_SatisfiesP
import Definitions.Def_ClawFreeChoosable_SatisfiesM

set_option autoImplicit false

open Classical

namespace ClawFreeChoosable

/-- **Lemma 7.3 (Simplicial cliques)** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.10). Let `S` be a clique of simplicial vertices
in a graph `G`, and put `Q = N_G(S)`. Then the vertices of `S` are pairwise true twins and
`S ∪ Q` is a clique. Moreover, if `G` is claw-free, then:
(a) the clique `Q` is attachable in `G − S`;
(b) given a (Pk)-instance `(G, S, ϕ, L)`, define lists on `G − S` by
`L′(v) := L(v) \ ϕ(S)` for `v ∈ Q` and `L′(v) := L(v)` for `v ∉ S ∪ Q`. Then
`(G − S, Q, |S|, L′)` is an (Mk)-instance, and it is colorable if and only if `(G, S, ϕ, L)` is
colorable.

**Formalization Note.** `G − S` is `G.induce Sᶜ`, whose vertices are the elements `x` of the
subtype `Sᶜ`; `Q` and `L′` are read on it through `x.1`. A (Pk)-instance presupposes
`k ≥ ω(G)` (Definition 7.2), carried as `G.cliqueNum ≤ k`. Colorability of the (Mk)-instance is
the published `ListColorable`. -/
theorem lemma_7_3_simplicial_cliques {V : Type} [Fintype V] (G : SimpleGraph V) (S : Set V)
    (hS : IsSimplicialClique G S) :
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → TrueTwins G u v) ∧ G.IsClique (S ∪ extNbhd G S) ∧
    (IsClawFree G →
      IsAttachable (G.induce Sᶜ) {x | x.1 ∈ extNbhd G S} ∧
      ∀ (k : ℕ) (α : Type) (ϕ : V → α) (L : V → Finset α),
        G.cliqueNum ≤ k → IsPInstance G k S ϕ L →
        IsMInstance (G.induce Sᶜ) k {x | x.1 ∈ extNbhd G S} S.ncard
            (fun x : (Sᶜ : Set V) =>
              if x.1 ∈ extNbhd G S then (L x.1).filter (fun c => c ∉ ϕ '' S) else L x.1) ∧
          (OAI.LinearListHadwiger.ListColorable (G.induce Sᶜ)
              (fun x : (Sᶜ : Set V) =>
                if x.1 ∈ extNbhd G S then (L x.1).filter (fun c => c ∉ ϕ '' S) else L x.1) ↔
            PColorable G S ϕ L)) := by sorry

end ClawFreeChoosable
