-- Prove2me | Theorems.Thm_DynEdgeOrient_claim_4_14
-- name    : DynEdgeOrient.claim_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:52.426542+00:00
-- url     : https://prove2.me/theorems/ae39e842-d11c-40b8-9565-4a6972563674
-- title:
--   Claim 4.14: $\sum_{V^{\mathrm{int}}(H)}\bigl(\alpha|X(I)|+|E(A(I),B(I))|\bigr)=O(\alpha|U|)$
-- statement:
--   Let the dynamic graph and its hierarchy be as in Lemma 4.9 ($|U|=2^K$ arboricity $\alpha$-preserving updates, $G_0$ arbitrary). There is an absolute constant $C$ such that
--
--   $$
--   \sum_{(S,I)\in V^{\mathrm{int}}(H)}\bigl(\alpha|X(I)|+|E(A(I),B(I))|\bigr)\ \le\ C\,\alpha\,|U| .
--   $$
--
--   The bound yields clauses 1 and 4 of Lemma 4.9 (Corollaries 4.15 and 4.16).
--
--   **Formalization Note** The proof gives $2\sum\le(4\alpha-1)|U|$.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
--   - reading: |E(A(I), B(I))| with no time specified → counted in G_{i−1}; reason: Remark 4.10: the count is constant throughout I, so the page leaves the time unspecified
--   - reading: Σ_{(S,I)∈V^int(H)} α|X(I)| + |E(A(I), B(I))| → Σ (α|X(I)| + |E(A(I), B(I))|); reason: the proof sums both terms over the internal nodes ("2 Σ α|X(I)| + |E(A(I), B(I))| ≤ Ψ(0)")
--   - encoding: O(α|U|) → ≤ C·α·2^K with C absolute and chosen first; reason: the O-constant does not depend on α, the graph or |U|
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Claim 4.14, p.17 (pdf p.18)

import Mathlib
import Definitions.Def_DynEdgeOrient_NodeQuantities

namespace DynEdgeOrient

/-- **Claim 4.14** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Claim 4.14,
p.17). For the hierarchy of Lemma 4.9,
`Σ_{(S,I) ∈ V^int(H)} (α|X(I)| + |E(A(I), B(I))|) = O(α|U|)`.

**Formalization Note.** `O(·)` is one absolute constant `C`, chosen before the graph, `α` and
`K`. Stated for the constructed hierarchy `hierS` of a dynamic graph with `|U| = 2^K`
arboricity-`α`-preserving updates (`G_0` arbitrary). The internal nodes are `(ℓ, q)` with
`1 ≤ ℓ ≤ K`, `q < 2^(K−ℓ)`. The sum is read as `Σ (α|X| + |E(A, B)|)`, as the proof sums it; the
proof gives `2 Σ ≤ (4α − 1)|U|`. -/
theorem claim_4_14 :
    ∃ C : ℝ, ∀ (V E : Type*) [Fintype V] [DecidableEq V] [DecidableEq E]
      (ends : E → V × V) (_ : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E),
      IsDynamic G (2 ^ K) → ArbPreserving ends G (2 ^ K) α →
      ((∑ ℓ ∈ Finset.Icc 1 K, ∑ q ∈ Finset.range (2 ^ (K - ℓ)),
          (α * (Xset ends G α ℓ q).card + crossAB ends G α ℓ q) : ℕ) : ℝ) ≤
        C * α * 2 ^ K := by sorry

end DynEdgeOrient
