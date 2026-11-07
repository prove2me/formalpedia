-- Prove2me | Theorems.Thm_DynEdgeOrient_lemma_5_2
-- name    : DynEdgeOrient.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:35.853192+00:00
-- url     : https://prove2.me/theorems/2b5e0bc9-a59c-444e-99a0-9da0c6931ef2
-- title:
--   Lemma 5.2: $(5\alpha-2)$-orientations inside a node with $O\bigl(\sum_{\mathrm{desc}(S,I)}\Gamma(I')\log(\alpha|S'|/\Gamma(I'))\bigr)$ reorientations
-- statement:
--   Let the dynamic graph and its hierarchy be as in Lemma 4.9 ($2^K$ arboricity $\alpha$-preserving updates, $G_0$ arbitrary), and let $(S,I=[i,k))$ be a node. There is an absolute constant $C$ such that:
--
--   1. if $(S,I)$ is a leaf, then for every orientation under which each $v\in S$ has out-degree at most $5\alpha-2$ inside $G_{i-1}[S]$, there is an orientation with out-degrees at most $5\alpha-2$ inside $G_i[S]$ that agrees with the first on every edge of both $G_{i-1}[S]$ and $G_i[S]$ (no reorientation);
--   2. if $(S,I)$ is internal, then for every orientation with out-degrees at most $5\alpha-2$ inside $G_{i-1}[S]$, there is a sequence of orientations of $G_i[S],\dots,G_{k-1}[S]$, each with out-degrees at most $5\alpha-2$ inside $S$ and starting from the given one, whose total number of edge reorientations inside $S$ is at most
--
--   $$
--   C\sum_{(S',I')\in\mathrm{desc}(S,I)}\Gamma(I')\,\log_2\frac{\alpha|S'|}{\Gamma(I')} ,
--   $$
--
--   where $\mathrm{desc}(S,I)$ is the set of internal descendants of $(S,I)$, itself included.
--
--   This is the core of the flip bound: Lemma 5.7 applies clause 2 at the root and sums the right side with the log sum inequality.
--
--   **Formalization Note** A term with $\Gamma(I')=0$ is $0$. The base of the logarithm changes only $C$.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
--   - reading: |E(A(I), B(I))| with no time specified → counted in G_{i−1}; reason: Remark 4.10: the count is constant throughout I, so the page leaves the time unspecified
--   - encoding: 5α − 2 → 5 * α - 2 in ℕ; reason: equal for α ≥ 1; at α = 0 arboricity 0 forbids every edge, so no update exists and the statements are vacuous, and the paper never considers α = 0
--   - reading: clause 1: a (5α − 2)-orientation on G_{k=i+1}[S] → on G_i[S] = G_{k−1}[S]; reason: the leaf's interval [i, i+1) holds the single update u_i, so its last state is G_i, as in clause 2 ("G_i[S], …, G_{k−1}[S]"); the base case of the proof checks G_{i−1}[S] and G_i[S]
--   - encoding: "does not require any edge reorientations" → the new orientation agrees with the old one on every edge of both G_{i−1}[S] and G_i[S]; reason: an inserted edge's direction is free
--   - encoding: "less than O(Σ Γ(I′) log(α|S′|/Γ(I′)))" → ≤ C·Σ Γ(I′)·log₂(α|S′|/Γ(I′)), one absolute C chosen first for both clauses; reason: the O-constant is uniform; a Γ(I′) = 0 term is 0 in Lean (0·log(x/0) = 0) and in the paper's convention
--   - encoding: the total number of edge reorientations of the sequence of orientations → Σ_t flipsIn: for each transition t → t+1, the edges of G_t[S] ∩ G_{t+1}[S] whose direction differs between σ t and σ (t+1); reason: an inserted edge has no previous direction and a deleted one no next; flipping the differing edges of each transition one by one is a flip sequence with that many flips, and every flip sequence between the two orientations flips at least those edges
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Lemma 5.2, p.19 (pdf p.20)

import Mathlib
import Definitions.Def_DynEdgeOrient_NodeQuantities
import Definitions.Def_DynEdgeOrient_Orientation

namespace DynEdgeOrient

/-- **Lemma 5.2** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Lemma 5.2,
p.19). Let `G`, `U` and `H` be as in Lemma 4.9 and `(S, I = [i, k)) ∈ V(H)`.
1. If `(S, I)` is a leaf, then for any initial `(5α − 2)`-orientation on `G_{i−1}[S]` there is a
   `(5α − 2)`-orientation on `G_i[S]` that does not require any edge reorientations.
2. If `(S, I)` is internal, then for any initial `(5α − 2)`-orientation on `G_{i−1}[S]` there is a
   sequence of `(5α − 2)`-orientations on `G_i[S], …, G_{k−1}[S]` whose total number of edge
   reorientations is at most `O(Σ_{(S',I') ∈ desc(S,I)} Γ(I') log(α|S'| / Γ(I')))`.

**Formalization Note.**
* Hierarchy `hierS` of a dynamic graph with `2^K` arboricity-`α`-preserving updates (`G_0`
  arbitrary). Leaves are `(0, q)`, `q < 2^K`, with times `i − 1 = q`, `i = q + 1`; internal nodes
  are `(ℓ, q)`, `1 ≤ ℓ ≤ K`, `q < 2^(K−ℓ)`, with times `i − 1 = winLo ℓ q`, `k − 1 = winHi ℓ q`.
* Orientations and out-degrees are inside the induced subgraphs `G_t[S]`; a
  `(5α − 2)`-orientation of `G_t[S]` bounds the out-degree inside `G_t[S]` of every `v ∈ S`.
* Clause 1: the page prints `G_{k=i+1}[S]`; the leaf's interval `[i, i+1)` holds the one update
  `u_i`, so the state is `G_i = G_{k−1}`, as in clause 2. "Does not require any edge
  reorientations": the new orientation agrees with the old one on every edge of both
  `G_{i−1}[S]` and `G_i[S]`.
* Clause 2: the orientations form `σ : ℕ → E → Bool`, with `σ (i−1)` equal to the initial one on
  `G_{i−1}[S]`; the reorientations are the in-`S` flips of the transitions `t → t+1`,
  `i − 1 ≤ t < k − 1`.
* "Less than `O(·)`" is `≤ C · (·)` with one absolute constant `C`, chosen first, for both
  clauses. Base-2 logarithm (another base changes `C`). A term with `Γ(I') = 0` is `0`, both in
  Lean (`0 · log(x/0) = 0`) and in the paper's convention. -/
theorem lemma_5_2 :
    ∃ C : ℝ, ∀ (V E : Type*) [Fintype V] [DecidableEq V] [DecidableEq E]
      (ends : E → V × V) (_ : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E),
      IsDynamic G (2 ^ K) → ArbPreserving ends G (2 ^ K) α →
      (∀ q < 2 ^ K, ∀ σ₀ : E → Bool,
        (∀ v ∈ hierS ends G α 0 q, outDegIn ends (G q) (hierS ends G α 0 q) σ₀ v ≤ 5 * α - 2) →
        ∃ σ₁ : E → Bool,
          (∀ v ∈ hierS ends G α 0 q,
            outDegIn ends (G (q + 1)) (hierS ends G α 0 q) σ₁ v ≤ 5 * α - 2) ∧
          ∀ e ∈ edgesIn ends (G q) (hierS ends G α 0 q) ∩
              edgesIn ends (G (q + 1)) (hierS ends G α 0 q), σ₁ e = σ₀ e) ∧
      (∀ ℓ q, 1 ≤ ℓ → ℓ ≤ K → q < 2 ^ (K - ℓ) → ∀ σ₀ : E → Bool,
        (∀ v ∈ hierS ends G α ℓ q,
          outDegIn ends (G (winLo ℓ q)) (hierS ends G α ℓ q) σ₀ v ≤ 5 * α - 2) →
        ∃ σ : ℕ → E → Bool,
          (∀ e ∈ edgesIn ends (G (winLo ℓ q)) (hierS ends G α ℓ q), σ (winLo ℓ q) e = σ₀ e) ∧
          (∀ t, winLo ℓ q < t → t ≤ winHi ℓ q → ∀ v ∈ hierS ends G α ℓ q,
            outDegIn ends (G t) (hierS ends G α ℓ q) (σ t) v ≤ 5 * α - 2) ∧
          ((∑ t ∈ Finset.Ico (winLo ℓ q) (winHi ℓ q),
              flipsIn ends (G t) (G (t + 1)) (hierS ends G α ℓ q) (σ t) (σ (t + 1)) : ℕ) : ℝ) ≤
            C * ∑ p ∈ desc ℓ q, (Gamma ends G α p.1 p.2 : ℝ) *
              Real.logb 2 ((α : ℝ) * (hierS ends G α p.1 p.2).card / Gamma ends G α p.1 p.2)) := by sorry

end DynEdgeOrient
