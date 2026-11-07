-- Prove2me | Theorems.Thm_DynEdgeOrient_claim_4_11
-- name    : DynEdgeOrient.claim_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:50.937589+00:00
-- url     : https://prove2.me/theorems/4b456aa9-eca3-4eaf-b0c3-906c698b57c0
-- title:
--   Claim 4.11: the hierarchy constructed in Lemma 4.9 is special
-- statement:
--   Let $G_0,\dots,G_{2^K}$ be a dynamic loop-free multigraph undergoing an arboricity $\alpha$-preserving sequence of $2^K$ edge insertions and deletions, where $G_0$ need not be empty. Then every node $(S,I)$ of the DIS hierarchy constructed in the proof of Lemma 4.9 is
--
--   1. **total**: every edge inserted or deleted during $I$ has both endpoints in $S$, and
--   2. **nearly isolated**: no vertex outside $S$ has $2\alpha$ or more edges into $S$ at any time of the window of $I$.
--
--   Near isolation is what lets each node's flips stay inside its own vertex set. It is the first part of Lemma 4.9.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Claim 4.11, p.14 (pdf p.15)

import Mathlib
import Definitions.Def_DynEdgeOrient_Hierarchy

namespace DynEdgeOrient

/-- **Claim 4.11** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Claim 4.11,
p.14): "H is special."

Let `G_0, …, G_m` be a dynamic loop-free multigraph undergoing an arboricity-`α`-preserving
sequence of `m = 2^K` edge insertions and deletions, with `G_0` arbitrary. Then every node of the
DIS hierarchy `hierS` constructed in the proof of Lemma 4.9 is total and nearly isolated on its
window.

**Formalization Note.** The hierarchy is the paper's construction, not an arbitrary hierarchy;
windows include both ends (`winLo`, `winHi`); see `DynEdgeOrient.Hierarchy`. -/
theorem claim_4_11 {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → V × V) (hends : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E)
    (hdyn : IsDynamic G (2 ^ K)) (harb : ArbPreserving ends G (2 ^ K) α) :
    IsSpecial ends G α K := by sorry

end DynEdgeOrient
