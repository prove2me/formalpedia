-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_6_14
-- name    : AgnosticTNS.Supplement.theorem_6_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:48:50.823369+00:00
-- url     : https://prove2.me/theorems/ba2e0a28-ba34-4f5c-9683-921ec7142ba3
-- title:
--   Theorem 6.14 — rerouting to a TTN on a tree-cut decomposition
-- statement:
--   Let $G=([n],E)$, $w:E\to\mathbb N$, and let $(\mathcal T,\mathcal X)$ be a tree-cut decomposition of $G$ of width at most $k\ge1$. Let $(\hat T,\hat{\mathcal X})$ be a tree-indexed partition obtained from it by removing empty bags as in Lemma 6.13, $m=|V(\hat T)|$, and for every edge $f$ of $\hat T$ let $w_{\hat T}(f)=\prod_{e\in\mathrm{cut}_G(A_f)}w(e)$ (6.30), $A_f$ the union of the bags on one side of $\hat T-f$. Then:
--   1. for every $|\psi\rangle\in S_d(G,w)$, after grouping each bag into one physical subsystem (6.31) and padding to dimension $d^k$, $|\psi\rangle_{\hat{\mathcal X}}\in S_{d^k}(\hat T,w_{\hat T})$ (6.32);
--   2. if $w(e)\le\chi$ for every edge ($\chi\ge1$) then $w_{\hat T}(f)\le\chi^k$ for every edge $f$ of $\hat T$ (6.33); hence every state of $S_d(G,\chi)$ is mapped into $S_{d^k}(\hat T,\chi^k)$;
--   3. $\lceil n/k\rceil\le m\le n$ (6.34);
--   4. for an optimal tree-cut decomposition (width $\mathrm{tcw}(G)$) the same holds with $k=\mathrm{tcw}(G)$.
--
--   Tree-cutwidth thus bounds both the grouped physical dimension and the bond dimension of a TTN representation of any tensor network state.
--
--   **Formalization Note** The statement is quantified over every tree-indexed partition satisfying conclusions 1–2 of Lemma 6.13; the grouping lists the vertices of each bag in increasing order and uses base-$d$ digits.
--
--   Differences from the source:
--   - generalization: a tree-cut decomposition of width k ≥ 1 → of width at most k (k ≥ 1); reason: every conclusion is monotone in k; a decomposition of width exactly k is a special case
--   - generalization: the tree-indexed partition obtained by removing empty bags as in Lemma 6.13 → every tree-indexed partition into nonempty bags satisfying Lemma 6.13's conclusions 1–2 (IsEmptyBagRemoval); reason: every outcome of the empty-bag removal satisfies them, so the source's partition is covered
--   - reading: tor(t) = |V(H̃_t)|, the size of the 3-centre of the torso → the least vertex count over all terminal results of the suppression process (tor); reason: the 3-centre is unique in the literature, so the values agree; the minimum makes the width hypothesis the weakest reading
--   - encoding: (6.33) if w(e) ≤ χ for every edge → with 1 ≤ χ; reason: standing assumption χ ≥ 1 (p.2); for χ = 0 an edge of T̂ with empty cut would have w_T̂ = 1 > 0^k
--   - encoding: canonical identification (6.31) and padding to d^k → groupState: bag vertices in increasing order, base-d digits, zero amplitude on padding; reason: any fixed bag-local injective identification is equivalent
--   - reading: if no decomposition is given, one may compute one of width ≤ 2 tcw(G) in time 2^{O(tcw(G)² log tcw(G))} n², and the statement holds with k = 2 tcw(G) → the time bound is not stated; the k = 2 tcw(G) statement is the first conjunct at that k; reason: the time bound is [Kim+18]'s, cited and not proved in the paper
--   - encoding: ⌈n/k⌉ ≤ m → ⌈(n : ℝ)/k⌉₊ ≤ m; reason: the same quantity
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.14, Eqs. (6.30)–(6.34), p.56; Lemma 6.13, p.55

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_tcw
import Definitions.Def_AgnosticTNS_Supplement_IsEmptyBagRemoval
import Definitions.Def_AgnosticTNS_Supplement_wTree
import Definitions.Def_AgnosticTNS_Supplement_groupState
import Definitions.Def_AgnosticTNS_TNSchi

namespace AgnosticTNS.Supplement

/-- **Theorem 6.14 (Rerouting to a TTN)**, p.56 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Let `G = ([n], E)`, `w : E → ℕ`, `|ψ⟩ ∈ S_d(G, w)`, and `(𝒯, X)` a tree-cut decomposition of `G` of width
`k ≥ 1`. Let `(T̂, X̂)` be the tree-indexed partition obtained by removing empty bags as in Lemma 6.13,
`m = |V(T̂)|`. With `w_T̂(f) = ∏_{e ∈ cut_G(A_f)} w(e)` (6.30), under the canonical identification (6.31)
and after padding the grouped local spaces to dimension `d^k`, `|ψ⟩_X̂ ∈ S_{d^k}(T̂, w_T̂)` (6.32). If
`w(e) ≤ χ` for every edge then `w_T̂(f) ≤ χ^k` (6.33) for every `f ∈ E(T̂)`; hence every state in `S_d(G, χ)`
has a representation in `S_{d^k}(T̂, χ^k)`. Moreover `⌈n/k⌉ ≤ m ≤ n` (6.34). In particular, for an optimal
tree-cut decomposition one may take `k = tcw(G)`.

**Formalization Note** "Of width `k`" is read as width at most `k` (every conclusion is monotone in `k`).
`(T̂, X̂)` ranges over every tree-indexed partition satisfying Lemma 6.13's conclusions 1–2
(`IsEmptyBagRemoval`); every outcome of the empty-bag removal does. `χ ≥ 1` (standing, p.2). The
`k = tcw(G)` clause is the second conjunct (decompositions of width `tcw(G)`). The sentence on computing a
width-`2 tcw(G)` decomposition in time `2^{O(tcw(G)² log tcw(G))} n²` cites [Kim+18] and is not stated;
the statement for `k = 2 tcw(G)` is the first conjunct at that `k`. -/
theorem theorem_6_14 :
    (∀ (n d k m : ℕ) (G : SimpleGraph (Fin n)) (D : TreeCutDecomp n) (That : SimpleGraph (Fin m))
      (Xhat : Fin m → Finset (Fin n)),
      1 ≤ k → tcWidth G D ≤ k → IsEmptyBagRemoval D That Xhat →
      (∀ (w : G.edgeSet → ℕ) (ψ : (Fin n → Fin d) → ℂ), ψ ∈ TNS d G w →
        groupState d k Xhat ψ ∈ TNS (d ^ k) That (wTree G w That Xhat)) ∧
      (∀ (w : G.edgeSet → ℕ) (χ : ℕ), 1 ≤ χ → (∀ e, w e ≤ χ) →
        ∀ f, wTree G w That Xhat f ≤ χ ^ k) ∧
      (∀ χ : ℕ, 1 ≤ χ → ∀ ψ ∈ TNSchi d G χ, groupState d k Xhat ψ ∈ TNSchi (d ^ k) That (χ ^ k)) ∧
      ⌈(n : ℝ) / (k : ℕ)⌉₊ ≤ m ∧ m ≤ n) ∧
    (∀ (n d m : ℕ) (G : SimpleGraph (Fin n)) (D : TreeCutDecomp n) (That : SimpleGraph (Fin m))
      (Xhat : Fin m → Finset (Fin n)),
      tcWidth G D = tcw G → IsEmptyBagRemoval D That Xhat →
      (∀ (w : G.edgeSet → ℕ) (ψ : (Fin n → Fin d) → ℂ), ψ ∈ TNS d G w →
        groupState d (tcw G) Xhat ψ ∈ TNS (d ^ (tcw G)) That (wTree G w That Xhat)) ∧
      (∀ (w : G.edgeSet → ℕ) (χ : ℕ), 1 ≤ χ → (∀ e, w e ≤ χ) →
        ∀ f, wTree G w That Xhat f ≤ χ ^ (tcw G)) ∧
      (∀ χ : ℕ, 1 ≤ χ → ∀ ψ ∈ TNSchi d G χ, groupState d (tcw G) Xhat ψ ∈ TNSchi (d ^ (tcw G)) That (χ ^ (tcw G))) ∧
      ⌈(n : ℝ) / ((tcw G) : ℕ)⌉₊ ≤ m ∧ m ≤ n) := by sorry

end AgnosticTNS.Supplement
