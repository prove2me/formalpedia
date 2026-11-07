-- Prove2me | Theorems.Thm_DynEdgeOrient_lemma_5_4
-- name    : DynEdgeOrient.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:51.306113+00:00
-- url     : https://prove2.me/theorems/0571e7d7-6f9d-41a5-880b-21ec9fb76134
-- title:
--   Lemma 5.4: before Steps 1 and 4, $|\vec E_{G_{i-1}}(S_1,S\setminus S_1)|$ and $|\vec E_{G_{j-1}}(S_2,S\setminus S_2)|$ are $O(\Gamma(I))$
-- statement:
--   Let the dynamic graph and its hierarchy be as in Lemma 4.9 ($2^K$ arboricity $\alpha$-preserving updates, $G_0$ arbitrary), and let $(S,I=[i,k))$ be an internal node with children $(S_1,[i,j))$ and $(S_2,[j,k))$. There is an absolute constant $C$ such that:
--
--   1. for every orientation of $G_{i-1}$ under which every $v\in S$ has out-degree at most $5\alpha-2$ inside $G_{i-1}[S]$, the number of edges directed from $S_1$ to $S\setminus S_1$ satisfies $|\vec E_{G_{i-1}}(S_1,S\setminus S_1)|\le C\,\Gamma(I)$;
--   2. for every orientation of $G_{j-1}$ under which every $v\in S$ has out-degree at most $5\alpha-2$ inside $G_{j-1}[S]$, $|\vec E_{G_{j-1}}(S_2,S\setminus S_2)|\le C\,\Gamma(I)$.
--
--   Here $\Gamma(I)=\alpha|X(I)|+\alpha|Y(I)|+|E(A(I),B(I))|$. The lemma bounds the excess handed to Lemma 3.1 and the flips of Steps 2 and 5 in the proof of Lemma 5.2.
--
--   **Formalization Note** The proof gives $|E(A,B)|+(2\alpha-1)|X|+(5\alpha-2)|Y|\le5\Gamma$.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
--   - reading: |E(A(I), B(I))| with no time specified → counted in G_{i−1}; reason: Remark 4.10: the count is constant throughout I, so the page leaves the time unspecified
--   - encoding: 5α − 2 → 5 * α - 2 in ℕ; reason: equal for α ≥ 1; at α = 0 arboricity 0 forbids every edge, so no update exists and the statements are vacuous, and the paper never considers α = 0
--   - generalization: the orientation held before Step 1 (resp. Step 4) of the procedure of Lemma 5.2 → every orientation whose out-degrees inside G_{i−1}[S] (resp. G_{j−1}[S]) are ≤ 5α − 2 on S; reason: the proof uses only that G[S] is (5α − 2)-oriented before the step, and the procedure's orientation is one of these
--   - encoding: O(Γ(I)) → ≤ C·Γ(I), one absolute C chosen first for both bounds; reason: the O-constant is uniform over the hierarchy
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Lemma 5.4, p.20 (pdf p.21)

import Mathlib
import Definitions.Def_DynEdgeOrient_NodeQuantities
import Definitions.Def_DynEdgeOrient_Orientation

namespace DynEdgeOrient

/-- **Lemma 5.4** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Lemma 5.4,
p.20). At an internal node `(S, I = [i, k))` of the hierarchy of Lemma 4.9 with children
`(S₁, [i, j))`, `(S₂, [j, k))`: before Step 1, `|E⃗_{G_{i−1}}(S₁, S ∖ S₁)| = O(Γ(I))`; before
Step 4, `|E⃗_{G_{j−1}}(S₂, S ∖ S₂)| = O(Γ(I))`.

**Formalization Note.**
* The page states the bounds for the orientation that the procedure of Lemma 5.2 holds before
  Steps 1 and 4; its proof uses only that `G_{i−1}[S]` (resp. `G_{j−1}[S]`) is
  `(5α − 2)`-oriented. The Lean states both bounds for **every** orientation `σ` whose out-degrees
  inside `G_{i−1}[S]` (resp. `G_{j−1}[S]`) are at most `5α − 2` at every vertex of `S`.
* One absolute constant `C` for both bounds, chosen first. The proof gives
  `|E(A,B)| + (2α − 1)|X| + (5α − 2)|Y| ≤ 5Γ`.
* Hierarchy `hierS` of a dynamic graph with `2^K` arboricity-`α`-preserving updates (`G_0`
  arbitrary); internal nodes `1 ≤ ℓ ≤ K`, `q < 2^(K−ℓ)`; `5α − 2` in `ℕ`. -/
theorem lemma_5_4 :
    ∃ C : ℝ, ∀ (V E : Type*) [Fintype V] [DecidableEq V] [DecidableEq E]
      (ends : E → V × V) (_ : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E),
      IsDynamic G (2 ^ K) → ArbPreserving ends G (2 ^ K) α →
      ∀ ℓ q, 1 ≤ ℓ → ℓ ≤ K → q < 2 ^ (K - ℓ) →
        (∀ σ : E → Bool,
          (∀ v ∈ hierS ends G α ℓ q,
            outDegIn ends (G (winLo ℓ q)) (hierS ends G α ℓ q) σ v ≤ 5 * α - 2) →
          (dirCount ends (G (winLo ℓ q)) σ (child₁ ends G α ℓ q)
              (hierS ends G α ℓ q \ child₁ ends G α ℓ q) : ℝ) ≤
            C * Gamma ends G α ℓ q) ∧
        (∀ σ : E → Bool,
          (∀ v ∈ hierS ends G α ℓ q,
            outDegIn ends (G (winMid ℓ q)) (hierS ends G α ℓ q) σ v ≤ 5 * α - 2) →
          (dirCount ends (G (winMid ℓ q)) σ (child₂ ends G α ℓ q)
              (hierS ends G α ℓ q \ child₂ ends G α ℓ q) : ℝ) ≤
            C * Gamma ends G α ℓ q) := by sorry

end DynEdgeOrient
