-- Prove2me | Theorems.Thm_DynEdgeOrient_claim_4_13
-- name    : DynEdgeOrient.claim_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:28.609362+00:00
-- url     : https://prove2.me/theorems/920be990-c664-4a8e-9c64-0430381bfc09
-- title:
--   Claim 4.13: $\Psi(\ell-1)-\Psi(\ell)\ge2\sum_{V^\ell(H)}(\alpha|X(I)|+|E(A(I),B(I))|)$
-- statement:
--   Let the dynamic graph and its hierarchy be as in Lemma 4.9 ($2^K$ arboricity $\alpha$-preserving updates, $G_0$ arbitrary). For a node $(S,I=[i,k))$ let $\psi(I)=2\alpha|S|-|E_{G_{i-1}}(S)|-|E_{G_{k-1}}(S)|$, and let $\Psi(\ell)$ be the sum of $\psi$ over the nodes of level $\ell$. For every level $1\le\ell\le K$,
--
--   $$
--   \Psi(\ell-1)-\Psi(\ell)\ \ge\ 2\sum_{(S,I)\in V^\ell(H)}\bigl(\alpha|X(I)|+|E(A(I),B(I))|\bigr).
--   $$
--
--   Summed over the levels, this gives Claim 4.14.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: an arboricity α-preserving sequence of updates (arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α, at every step) → ArbPreserving: |E_{G_t}(S)| ≤ α(|S| − 1) for every vertex set S and every t ≤ |U|, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - encoding: the DIS hierarchy H constructed in the proof of Lemma 4.9, with |U| a power of 2 → hierS with |U| = 2^K, node (ℓ, q) for I = [q·2^ℓ+1, (q+1)·2^ℓ+1), window of times [q·2^ℓ, (q+1)·2^ℓ]; reason: the construction's own indexing (proof of Lemma 4.9, step 2(a)i)
--   - reading: "during I" / "throughout I" for I = [i, k) → the states G_{i−1}, …, G_{k−1}, both ends of the window included; reason: Definition 4.1 and §2.1 describe (S, I) as the dynamic graph on G_{i−1}, …, G_{k−1}; Claim 4.11's base case checks the states before and after the update
--   - reading: step v: while some v ∉ S has |E(v, S)| ≥ 2α, add v to S → the least superset of S₁ ∪ S₂ such that no v outside it has |E(v, ·)| ≥ 2α at every time of the window; reason: the rule is monotone, so the loop ends at this least closed set in any order of additions; the page notes E(v, S) is time invariant on the window, and the claim 4.12 proof uses "≥ 2α throughout I"
--   - reading: |E(A(I), B(I))| with no time specified → counted in G_{i−1}; reason: Remark 4.10: the count is constant throughout I, so the page leaves the time unspecified
--   - encoding: integer inequalities between edge counts → in ℤ, with the ℕ counts cast; reason: the right sides contain −α|Y(I)|
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Claim 4.13, p.16 (pdf p.17)

import Mathlib
import Definitions.Def_DynEdgeOrient_NodeQuantities

namespace DynEdgeOrient

/-- **Claim 4.13** (Hiken–Wein, STOC 2027 submission, manuscript sha256 626b4eee…, Claim 4.13,
p.16). For any level `ℓ ≥ 1` of the hierarchy of Lemma 4.9,
`Ψ(ℓ − 1) − Ψ(ℓ) ≥ 2 Σ_{(S,I) ∈ V^ℓ(H)} (α|X(I)| + |E(A(I), B(I))|)`,
where `ψ(I) = 2α|S| − |E_{G_{i−1}}(S)| − |E_{G_{k−1}}(S)|` and `Ψ(ℓ)` is the sum of `ψ` over level `ℓ`.

**Formalization Note.** Stated for the constructed hierarchy `hierS` of a dynamic graph with
`m = 2^K` arboricity-`α`-preserving updates (`G_0` arbitrary); the levels are `1 ≤ ℓ ≤ K` and level
`ℓ` consists of the nodes `q < 2^(K−ℓ)`. In `ℤ`; `|E(A, B)|` is counted at time `i − 1`. -/
theorem claim_4_13 {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → V × V) (hends : ∀ e, (ends e).1 ≠ (ends e).2) (α K : ℕ) (G : ℕ → Finset E)
    (hdyn : IsDynamic G (2 ^ K)) (harb : ArbPreserving ends G (2 ^ K) α)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓK : ℓ ≤ K) :
    Psi ends G α K (ℓ - 1) - Psi ends G α K ℓ ≥
      2 * ∑ q ∈ Finset.range (2 ^ (K - ℓ)),
        ((α : ℤ) * (Xset ends G α ℓ q).card + crossAB ends G α ℓ q) := by sorry

end DynEdgeOrient
