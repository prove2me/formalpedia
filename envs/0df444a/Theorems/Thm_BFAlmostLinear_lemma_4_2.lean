-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_4_2
-- name    : BFAlmostLinear.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:41.956208+00:00
-- url     : https://prove2.me/theorems/7aea25b7-f8af-4a35-937a-3b5a1e37fc57
-- title:
--   Lemma 4.2 with Subclaims 4.3–4.5 — betweenness reduction through the auxiliary graph $G'$ (corrected: exact arc count)
-- statement:
--   Let $G$ be a weighted graph with frozen flags and levels satisfying (I1)–(I4), $U$ a set of negative vertices, $h\ge0$ a hop bound, and $M\ge0$ larger than $|\omega(e)|$ for every flagged arc $e$. Let $G'$ be the auxiliary graph of Lemma 4.2 built from $G,U,h,M$. Then:
--
--   1. **(Subclaim 4.3 and the reweighting.)** If $\phi'$ is a potential on $G'$ under which every arc of $G'$ other than its flagged auxiliary arcs has non-negative weight, then $\psi(v)=\phi'(v_0)$ is a valid potential on $G$, for all $r\in U$ and $s,t\in V$
--   $$\psi(t)-\psi(s)\le\tilde d^h(s,r)+\tilde d^h(r,t),$$
--   and after reweighting by $\psi$, $\tilde d^h_\psi(s,r)+\tilde d^h_\psi(r,t)\ge0$.
--   2. **(Subclaim 4.4.)** Every closed walk of negative weight in $G'$ avoiding flagged auxiliary arcs yields a closed walk in $G$ (auxiliary arcs allowed) of the same weight.
--   3. **(Invariants, Subclaim 4.5.)** $G'$ satisfies (I1)–(I4), copies keeping their levels and new vertices at level $0$; every arc of $G'$ that is not a copy of an arc of $G$ joins two vertices of level $0$.
--   4. **(Size.)** $G'$ has $(2h+1)|V|+2|U|$ vertices and $(2h+1)|E|+2h\cdot\#\{\text{flagged arcs}\}+2h\cdot|S_0|+3|U|$ arcs, and its real flagged arcs are exactly the $|U|$ arcs $r^{\mathrm{tail}}\to r^{\mathrm{head}}$.
--
--   So one shortest-path computation on $G'$ either finds a negative cycle or a valid reweighting that fixes $U$ for $\tilde d^h$, while keeping the invariants for recursion.
--
--   Differences from the source:
--   - reading: "there is an algorithm that … either reports a negative cycle … or finds a valid reweighting" → the two outcomes stated for the explicit $G'$ of pp.13–14, for every potential $\phi'$ meeting the hypothesis of Subclaim 4.3 and for every negative closed walk; reason: the lemma says the algorithm "computes this reweighting by solving the single-source shortest path problem on an auxiliary graph $G'$".
--   - reading: "a valid potential $\phi$ neutralizing all negative edges in $G'$" (Subclaim 4.3) → non-negative on every arc of $G'$ except flagged auxiliary arcs; reason: validity covers the non-negative arcs, neutralizing covers the real negative arcs.
--   - generalization: "a negative cycle in $G'$" → any negative closed walk of $G'$ avoiding flagged auxiliary arcs (unflagged auxiliary arcs allowed); reason: the shortest-path computation ignores auxiliary arcs, so its cycles are a special case.
--   - correction: "$O(h|E(G)|)$ extra edges" → the exact count $2h\cdot\#\{\text{flagged arcs}\}+2h|S_0|+3|U|$; reason: a graph with $n\ge1$ vertices, no arcs and $U=\emptyset$ satisfies (I1)–(I4) and gets $2hn$ self arcs, which is not $O(h\cdot0)$; the proof (p.16) says $O(nh)$.
--   - reading: $G'$ "along with the data structure for maintaining invariants in Lemma 3.1" → the data structure is not modelled; reason: it is an algorithmic object, and the copies contain every arc of $G$.
--   - encoding: $M$ "larger than the absolute value of any (real or auxiliary) negative edge weight", frozen flags → hypotheses $M\ge0$, $|\omega(e)|<M$ for flagged $e$, `Frozen`; reason: p.13 and §1.1.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 4.2, p.13; construction pp.13–14; Subclaims 4.3, 4.4, p.15; Subclaim 4.5 and size count, p.16

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1
import Definitions.Def_BFAlmostLinear_auxGraph

namespace BFAlmostLinear

open Classical in
/-- **Lemma 4.2**, p.13, with Subclaims 4.3–4.5, pp.15–16. "There is an algorithm that, given a graph G with vertex
partition S_0 ⊔ S_1 ⊔ · · · ⊔ S_t that satisfies invariants (I1)–(I4), a subset U ⊂ N of its negative vertices, and a hop
bound h, either reports a negative cycle in G or finds a valid reweighting ϕ such that after reweighting,
d̃^h(s, r) + d̃^h(r, t) ≥ 0 ∀r ∈ U, ∀s, t ∈ V. The algorithm computes this reweighting by solving the single-source
shortest path problem on an auxiliary graph G′ …"

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 4.2, p.13, Subclaims 4.3, 4.4, 4.5, pp.15–16.

**Formalization Note.** The algorithm is "solve SSSP on `auxGraph`". The statement has no machine; it states the two
outcomes on the explicit `G′` of pp.13–14, for every hop bound `h` (at `h = 0` the construction is one copy and
the gadget) and `M ≥ 0` above the absolute weight of each flagged arc:
* (a) If `ϕ` on `V(G′)` is nonnegative on every arc other than the auxiliary negatives, then `v ↦ ϕ(v₀)` is valid on
  `G`, Subclaim 4.3 holds, and `d̃^h + d̃^h ≥ 0` after the reweighting.
* (b) Subclaim 4.4: a closed walk of negative weight on the other arcs of `G′` gives a closed walk in `G` of the same
  weight, where auxiliary arcs may occur.
* (c) `G′` satisfies (I1)–(I4), with the levels of the copies and level `0` at each new vertex. Also Subclaim 4.5.
* (d) Exact counts. Printed: "O(h) copies", "O(|V(G)|) extra vertices, O(h|E(G)|) extra edges, and |U| real negative
  edges". The self edges are `2h |S₀|`, which the printed `O(h|E(G)|)` misses when `|S₀| > |E|` while the proof
  says `O(nh)`; the exact count avoids it. The data structure of Lemma 3.1 is not modeled. -/
theorem lemma_4_2 {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (level : V → ℕ)
    (U : Finset V) (h : ℕ) (M : ℝ) (hU : U ⊆ G.negVertices) (hF : G.Frozen)
    (hM0 : 0 ≤ M) (hM : ∀ e, G.neg e = true → |G.w e| < M)
    (hI1 : G.I1) (hI2 : G.I2 level) (hI3 : G.I3 level) (hI4 : G.I4 level) :
    let G' := auxGraph G level U h M
    -- (a) a potential on `G′` gives a valid reweighting of `G`, with Subclaim 4.3
    (∀ ϕ' : AuxVertex V U h → ℝ,
      (∀ a, ¬ (G'.aux a = true ∧ G'.neg a = true) → 0 ≤ (G'.reweight ϕ').w a) →
      let ψ : V → ℝ := fun v => ϕ' (.copy .base v)
      G.IsValid ψ ∧
      (∀ r ∈ U, ∀ s t, ((ψ t - ψ s : ℝ) : EReal) ≤ G.dHt h s r + G.dHt h r t) ∧
      (∀ r ∈ U, ∀ s t, 0 ≤ (G.reweight ψ).dHt h s r + (G.reweight ψ).dHt h r t)) ∧
    -- (b) Subclaim 4.4
    (∀ (v' : AuxVertex V U h) (P' : List (AuxArc G level U h)),
      G'.net.IsPathFrom v' v' P' → (∀ a ∈ P', ¬ (G'.aux a = true ∧ G'.neg a = true)) →
      pathWeight G'.w P' < 0 →
      ∃ (v : V) (P : List E), G.net.IsPathFrom v v P ∧ pathWeight G.w P = pathWeight G'.w P') ∧
    -- (c) the invariants of `G′`, and Subclaim 4.5
    (G'.I1 ∧ G'.I2 (auxLevel level) ∧ G'.I3 (auxLevel level) ∧ G'.I4 (auxLevel level)) ∧
    (∀ a, (∀ l e, a ≠ AuxArc.copy l e) →
      auxLevel level (G'.net.tail a) = 0 ∧ auxLevel level (G'.net.head a) = 0) ∧
    -- (d) sizes, and the real negative arcs
    Nat.card (AuxVertex V U h) = (2 * h + 1) * Fintype.card V + 2 * U.card ∧
    Nat.card (AuxArc G level U h) =
      (2 * h + 1) * Fintype.card E +
        2 * h * (Finset.univ.filter fun e => G.neg e = true).card +
        2 * h * (Finset.univ.filter fun v => level v = 0).card + 3 * U.card ∧
    (∀ a, (G'.neg a = true ∧ G'.aux a = false) ↔ ∃ r : U, a = AuxArc.gNeg r) := by sorry

end BFAlmostLinear
