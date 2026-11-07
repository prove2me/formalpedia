-- Prove2me | Theorems.Thm_DynEdgeOrient_lemma_4_9
-- name    : DynEdgeOrient.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:37.53299+00:00
-- url     : https://prove2.me/theorems/b6e6cd7a-6378-4ace-8b56-2df2b0bd2aed
-- title:
--   Lemma 4.9: the constructed DIS hierarchy is special, $\sum|X|,\sum|Y|=O(|U|)$, $\sum|S|=O(|U|\log|U|)$, $\sum|E(A,B)|=O(\alpha|U|)$
-- statement:
--   Let $G=G_0,\dots,G_{|U|}$ be a dynamic loop-free multigraph undergoing an arboricity $\alpha$-preserving sequence $U$ of edge insertions and deletions, where $G_0$ need not be empty and $|U|=2^K$ is a power of 2. Let $H$ be the DIS hierarchy constructed in the proof of the lemma. Then $H$ is special, and for an absolute constant $C$:
--
--   1. $\sum_{(S,I)\in V^{\mathrm{int}}(H)}|X(I)|\le C|U|$;
--   2. $\sum_{(S,I)\in V^{\mathrm{int}}(H)}|Y(I)|\le C|U|$;
--   3. $\sum_{(S,I)\in V(H)}|S|\le C\,|U|\,(\log_2|U|+1)$;
--   4. $\sum_{(S,I)\in V^{\mathrm{int}}(H)}|E(A(I),B(I))|\le C\alpha|U|$.
--
--   These four bounds give $\sum_I\Gamma(I)=O(\alpha|U|)$ and the total size of the hierarchy, which the log sum inequality turns into the $O(\alpha|U|\log\log|U|)$ bound of Lemma 5.7.
--
--   **Formalization Note** Clause 3 sums over all nodes, leaves included; $\log_2|U|+1$ is the number of levels. Clauses 1, 2 and 4 sum over the internal nodes.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
--   - reading: |E(A(I), B(I))| with no time specified → counted in G_{i−1}; reason: Remark 4.10: the count is constant throughout I, so the page leaves the time unspecified
--   - generalization: there is a special DIS hierarchy H with bounds 1–4 → the hierarchy constructed in the proof is special and satisfies 1–4; reason: it implies the existence statement, and Lemmas 5.2 and 5.7 use this H ("as described in Lemma 4.9")
--   - reading: O(|U|), O(|U| log |U|), O(α|U|) → one absolute C chosen first; C·|U|, C·|U|·(log₂|U| + 1), C·α·|U|; reason: log₂|U| + 1 is the number of levels (proof of Claim 4.18); it equals the asymptotic O(|U| log |U|) for |U| ≥ 2, and the literal |U| log |U| is 0 at |U| = 1, where Σ|S| = 2
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Lemma 4.9, p.14 (pdf p.15), with its proof pp.14–18

import Mathlib
import Definitions.Def_DynEdgeOrient_NodeQuantities

namespace DynEdgeOrient

/-- **Lemma 4.9** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Lemma 4.9,
p.14). Let `G = G_0, …, G_{|U|}` be a dynamic graph undergoing an arboricity-`α`-preserving
sequence `U` of edge insertions and deletions, `G_0` not necessarily empty, with `|U|` a power of 2.
There is a special DIS hierarchy `H` on `G` such that
1. `Σ_{V^int(H)} |X(I)| = O(|U|)`,
2. `Σ_{V^int(H)} |Y(I)| = O(|U|)`,
3. `Σ_{V(H)} |S| = O(|U| log |U|)`,
4. `Σ_{V^int(H)} |E(A(I), B(I))| = O(α|U|)`.

**Formalization Note.**
* The hierarchy is the one constructed in the proof (`hierS`), which is what Lemmas 5.2 and 5.7
  use ("H as described in Lemma 4.9"); stating the conclusion for it implies "there is".
* `|U| = 2^K`. Internal nodes: `1 ≤ ℓ ≤ K`, `q < 2^(K−ℓ)`; all nodes: `ℓ ≤ K` (leaves included in
  clause 3).
* One absolute constant `C` for all four bounds, chosen first. Clause 3 is
  `≤ C · |U| · (log₂|U| + 1)`, where `log₂|U| + 1` is the number of levels (proof of Claim 4.18);
  the literal `|U| log |U|` vanishes at `|U| = 1` although `Σ|S| = 2` there.
* `|E(A, B)|` is counted at time `i − 1` (`crossAB`; constant on the window by Remark 4.10). -/
theorem lemma_4_9 :
    ∃ C : ℝ, ∀ (V E : Type*) [Fintype V] [DecidableEq V] [DecidableEq E]
      (ends : E → V × V) (_ : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E),
      IsDynamic G (2 ^ K) → ArbPreserving ends G (2 ^ K) α →
      IsSpecial ends G α K ∧
      ((∑ ℓ ∈ Finset.Icc 1 K, ∑ q ∈ Finset.range (2 ^ (K - ℓ)),
          (Xset ends G α ℓ q).card : ℕ) : ℝ) ≤ C * 2 ^ K ∧
      ((∑ ℓ ∈ Finset.Icc 1 K, ∑ q ∈ Finset.range (2 ^ (K - ℓ)),
          (Yset ends G α ℓ q).card : ℕ) : ℝ) ≤ C * 2 ^ K ∧
      ((∑ ℓ ∈ Finset.range (K + 1), ∑ q ∈ Finset.range (2 ^ (K - ℓ)),
          (hierS ends G α ℓ q).card : ℕ) : ℝ) ≤
        C * 2 ^ K * (Real.logb 2 (2 ^ K) + 1) ∧
      ((∑ ℓ ∈ Finset.Icc 1 K, ∑ q ∈ Finset.range (2 ^ (K - ℓ)),
          crossAB ends G α ℓ q : ℕ) : ℝ) ≤ C * α * 2 ^ K := by sorry

end DynEdgeOrient
