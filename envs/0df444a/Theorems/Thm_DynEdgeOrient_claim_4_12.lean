-- Prove2me | Theorems.Thm_DynEdgeOrient_claim_4_12
-- name    : DynEdgeOrient.claim_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:01.094497+00:00
-- url     : https://prove2.me/theorems/d9cc7770-cab6-425b-bd2f-01ccf22217d4
-- title:
--   Claim 4.12: $|E_{G_{i-1}}(S)|$ and $|E_{G_{k-1}}(S)|$ bound the children's edges plus $|E(A,B)|+2\alpha|X|-\alpha|Y|$
-- statement:
--   Let the dynamic graph and its hierarchy be as in Lemma 4.9 ($2^K$ arboricity $\alpha$-preserving updates, $G_0$ arbitrary). Let $(S,I=[i,k))$ be an internal node with children $(S_1,[i,j))$ and $(S_2,[j,k))$. Then
--
--   $$
--   |E_{G_{i-1}}(S)|\ \ge\ |E_{G_{i-1}}(S_1)|+|E_{G_{j-1}}(S_2)|+|E(A(I),B(I))|+2\alpha|X(I)|-\alpha|Y(I)| \tag{3}
--   $$
--
--   $$
--   |E_{G_{k-1}}(S)|\ \ge\ |E_{G_{j-1}}(S_1)|+|E_{G_{k-1}}(S_2)|+|E(A(I),B(I))|+2\alpha|X(I)|-\alpha|Y(I)| \tag{4}
--   $$
--
--   Both inequalities feed Claim 4.13, the drop of the potential $\Psi$ from one level to the next.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
--   - reading: |E(A(I), B(I))| with no time specified → counted in G_{i−1}; reason: Remark 4.10: the count is constant throughout I, so the page leaves the time unspecified
--   - reading: (4): |E_{G_{k−1}}[S2])| → |E_{G_{k−1}}(S₂)|; reason: a misprint: (3) has the same term at time j−1 as |E_{G_{j−1}}(S2)|, and the proof treats (4) as (3) with S₁ and S₂ exchanged
--   - encoding: integer inequalities between edge counts → in ℤ, with the ℕ counts cast; reason: the right sides contain −α|Y(I)|
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Claim 4.12, p.15 (pdf p.16)

import Mathlib
import Definitions.Def_DynEdgeOrient_NodeQuantities

namespace DynEdgeOrient

/-- **Claim 4.12** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Claim 4.12,
p.15). For every internal node `(S, I = [i, k))` of the hierarchy of Lemma 4.9 with children
`(S₁, [i, j))`, `(S₂, [j, k))`:

  (3) `|E_{G_{i−1}}(S)| ≥ |E_{G_{i−1}}(S₁)| + |E_{G_{j−1}}(S₂)| + |E(A, B)| + 2α|X| − α|Y|`,
  (4) `|E_{G_{k−1}}(S)| ≥ |E_{G_{j−1}}(S₁)| + |E_{G_{k−1}}(S₂)| + |E(A, B)| + 2α|X| − α|Y|`.

**Formalization Note.** Stated for the constructed hierarchy `hierS` of a dynamic graph with
`2^K` arboricity-`α`-preserving updates (`G_0` arbitrary), at every internal node `(ℓ, q)`,
`1 ≤ ℓ ≤ K`, `q < 2^(K−ℓ)`. Times: `i − 1 = winLo ℓ q`, `j − 1 = winMid ℓ q`,
`k − 1 = winHi ℓ q`. Inequalities in `ℤ`. `|E(A, B)|` is counted at time `i − 1` (`crossAB`).
The page prints `|E_{G_{k−1}}[S2])|` in (4), read as `|E_{G_{k−1}}(S₂)|`. -/
theorem claim_4_12 {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → V × V) (hends : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E)
    (hdyn : IsDynamic G (2 ^ K)) (harb : ArbPreserving ends G (2 ^ K) α)
    (ℓ q : ℕ) (hℓ : 1 ≤ ℓ) (hℓK : ℓ ≤ K) (hq : q < 2 ^ (K - ℓ)) :
    ((edgesIn ends (G (winLo ℓ q)) (hierS ends G α ℓ q)).card : ℤ) ≥
        (edgesIn ends (G (winLo ℓ q)) (child₁ ends G α ℓ q)).card
        + (edgesIn ends (G (winMid ℓ q)) (child₂ ends G α ℓ q)).card
        + crossAB ends G α ℓ q + 2 * (α : ℤ) * (Xset ends G α ℓ q).card
        - (α : ℤ) * (Yset ends G α ℓ q).card ∧
      ((edgesIn ends (G (winHi ℓ q)) (hierS ends G α ℓ q)).card : ℤ) ≥
        (edgesIn ends (G (winMid ℓ q)) (child₁ ends G α ℓ q)).card
        + (edgesIn ends (G (winHi ℓ q)) (child₂ ends G α ℓ q)).card
        + crossAB ends G α ℓ q + 2 * (α : ℤ) * (Xset ends G α ℓ q).card
        - (α : ℤ) * (Yset ends G α ℓ q).card := by sorry

end DynEdgeOrient
