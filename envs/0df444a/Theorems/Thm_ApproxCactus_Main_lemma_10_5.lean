-- Prove2me | Theorems.Thm_ApproxCactus_Main_lemma_10_5
-- name    : ApproxCactus.Main.lemma_10_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:58.011814+00:00
-- url     : https://prove2.me/theorems/69881664-bb21-4a54-b69a-b59b274890a4
-- title:
--   Lemma 10.5 — ε-perturbing a symmetric γ-crossing-connected set compatibly with inversion keeps it (γ−2ε)-crossing-connected
-- statement:
--   Let $G$ be a finite graph and $\gamma,\varepsilon\in\mathbb N$ with $\gamma\ge2\varepsilon$. Let $S$ be a symmetric $\gamma$-crossing-connected set of separations of $G$. For each $s\in S$ let $s'$ be an $\varepsilon$-close separation of $G$, such that $(s^*)'=(s')^*$ for every $s\in S$. Then $S'=\{s':s\in S\}$ is $(\gamma-2\varepsilon)$-crossing-connected.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: for each s ∈ S a separation s′ → a function f on pairs, with s′ = f s and S′ = f '' S; reason: a choice of s′ for each s ∈ S is a function on S; values off S are irrelevant
--   - reading: "for every s ∈ S Denote S′" (missing period) → two sentences: the hypothesis (s∗)′ = (s′)∗ for s ∈ S, then the definition S′ := {s′ : s ∈ S}; reason: obvious typo in punctuation
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Lemma 10.5, printed p. 106 (PDF p. 109)

import Definitions.Def_ApproxCactus_Main_Crossing

namespace ApproxCactus.Main

/-- **Lemma 10.5**, p. 106: let `γ ≥ 2ε`, let `S` be a symmetric `γ`-crossing-connected set of
separations of `G`, and for each `s ∈ S` let `s'` be an `ε`-close separation of `G` with
`(s∗)' = (s')∗`. Then `S' := {s' : s ∈ S}` is `(γ − 2ε)`-crossing-connected. -/
theorem lemma_10_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (γ ε : ℕ)
    (hγε : 2 * ε ≤ γ) (S : Set (Finset V × Finset V)) (hS : ∀ s ∈ S, IsSep G s)
    (hsym : IsSymmetric S) (hcc : IsCrossingConnected γ S)
    (f : Finset V × Finset V → Finset V × Finset V)
    (hf : ∀ s ∈ S, IsSep G (f s) ∧ Close ε s (f s))
    (hinv : ∀ s ∈ S, f s.swap = (f s).swap) :
    IsCrossingConnected (γ - 2 * ε) (f '' S) := by sorry

end ApproxCactus.Main
