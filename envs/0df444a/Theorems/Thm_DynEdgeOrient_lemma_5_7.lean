-- Prove2me | Theorems.Thm_DynEdgeOrient_lemma_5_7
-- name    : DynEdgeOrient.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:52.330283+00:00
-- url     : https://prove2.me/theorems/2fa2de64-6d10-4e8a-a785-929b5558352e
-- title:
--   Lemma 5.7: at the root, $O(\alpha|U|\log\log|U|)$ flips keep out-degree $\le5\alpha-2$ inside $S$
-- statement:
--   Let $G$ be a dynamic loop-free multigraph undergoing an arboricity $\alpha$-preserving sequence $U$ of edge insertions and deletions with $|U|=2^K$ ($G_0$ arbitrary), and let $(S,I)$ be the root of the hierarchy constructed in Lemma 4.9. There is an absolute constant $C$ such that for every orientation of $G_0$ under which each $v\in S$ has out-degree at most $5\alpha-2$ inside $G_0[S]$, there is a sequence of orientations, starting from it on $G_0[S]$, such that after each update every $v\in S$ has out-degree at most $5\alpha-2$ in $S$, using at most
--
--   $$
--   C\,\alpha\,|U|\,\bigl(\log_2\log_2|U|+1\bigr)
--   $$
--
--   flips inside $S$ in total.
--
--   Applied to intervals of $p\approx n$ updates, it gives Theorem 1.2.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
--   - encoding: 5α − 2 → 5 * α - 2 in ℕ; reason: equal for α ≥ 1; at α = 0 arboricity 0 forbids every edge, so no update exists and the statements are vacuous, and the paper never considers α = 0
--   - generalization: a (5α − 2)-orientation G⃗_0 on G_0 → an orientation whose out-degrees inside G_0[S] are ≤ 5α − 2 on S; reason: every (5α − 2)-orientation of G_0 satisfies it, and the proof uses only out-degrees inside S
--   - reading: O(α|U| log log(|U|)) → ≤ C·α·|U|·(log₂log₂|U| + 1), C absolute and chosen first; reason: within a factor 2 of the literal form for |U| ≥ 4; at |U| ∈ {1, 2} the literal log log |U| is 0 in Lean (and undefined or 0 in ℝ), which the asymptotic O does not intend
--   - encoding: the number of flips of the sequence of orientations → Σ_t flipsIn: for each transition t → t+1, the edges of G_t[S] ∩ G_{t+1}[S] whose direction differs between σ t and σ (t+1); reason: an inserted edge has no previous direction and a deleted one no next; flipping the differing edges of each transition one by one is a flip sequence with that many flips, and every flip sequence between the two orientations flips at least those edges
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Lemma 5.7, p.22 (pdf p.23)

import Mathlib
import Definitions.Def_DynEdgeOrient_NodeQuantities
import Definitions.Def_DynEdgeOrient_Orientation

namespace DynEdgeOrient

/-- **Lemma 5.7** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Lemma 5.7,
p.22). Let `G` be a dynamic graph undergoing an arboricity-`α`-preserving sequence `U` of edge
insertions and deletions with `|U|` a power of 2, and let `(S, I)` be the root of the special DIS
hierarchy constructed as in Lemma 4.9. Given a `(5α − 2)`-orientation `G⃗_0` on `G_0`, there is a
sequence of `O(α|U| log log |U|)` flips so that after each update every `v ∈ S` has out-degree
`≤ 5α − 2` in `S`.

**Formalization Note.**
* `|U| = 2^K`, `G_0` arbitrary; the root is `S = hierS K 0`, with window `[0, 2^K]`.
* The hypothesis is only on `G_0[S]`: out-degrees inside `G_0[S]` at most `5α − 2` at every vertex
  of `S` (the proof uses nothing else). A `(5α − 2)`-orientation of `G_0` satisfies it.
* The flips are the in-`S` flips of the transitions `t → t+1`, `0 ≤ t < 2^K`, and `σ 0` equals the
  given orientation on `G_0[S]`.
* One absolute constant `C`, chosen first. The bound is `C · α · |U| · (log₂log₂|U| + 1)`: the
  literal `log log |U|` is `0` at `|U| = 2` although flips can be needed there; for `|U| ≥ 4` the
  two forms agree up to a factor 2. -/
theorem lemma_5_7 :
    ∃ C : ℝ, ∀ (V E : Type*) [Fintype V] [DecidableEq V] [DecidableEq E]
      (ends : E → V × V) (_ : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E),
      IsDynamic G (2 ^ K) → ArbPreserving ends G (2 ^ K) α →
      ∀ σ₀ : E → Bool,
        (∀ v ∈ hierS ends G α K 0,
          outDegIn ends (G 0) (hierS ends G α K 0) σ₀ v ≤ 5 * α - 2) →
        ∃ σ : ℕ → E → Bool,
          (∀ e ∈ edgesIn ends (G 0) (hierS ends G α K 0), σ 0 e = σ₀ e) ∧
          (∀ t, 1 ≤ t → t ≤ 2 ^ K → ∀ v ∈ hierS ends G α K 0,
            outDegIn ends (G t) (hierS ends G α K 0) (σ t) v ≤ 5 * α - 2) ∧
          ((∑ t ∈ Finset.range (2 ^ K),
              flipsIn ends (G t) (G (t + 1)) (hierS ends G α K 0) (σ t) (σ (t + 1)) : ℕ) : ℝ) ≤
            C * α * 2 ^ K * (Real.logb 2 (Real.logb 2 (2 ^ K)) + 1) := by sorry

end DynEdgeOrient
