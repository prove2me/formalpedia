-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_6_11
-- name    : AgnosticTNS.Supplement.theorem_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:47:48.579019+00:00
-- url     : https://prove2.me/theorems/5ddcb681-63df-45de-8693-d0e5fcc0edf6
-- title:
--   Theorem 6.11 — rerouting to an MPS along a linear ordering
-- statement:
--   Let $G=(V,E)$ with $V=[n]$, $w:E\to\mathbb N$, and $\pi:V\to[n]$ a linear ordering with $v_i=\pi^{-1}(i)$; let $P^\pi_n$ be the labelled path on $v_1,\dots,v_n$ with weights $w_P(\{v_i,v_{i+1}\})=\prod_{e\in\mathrm{cut}_G(\{v_1,\dots,v_i\})}w(e)$ (6.14). Then:
--   1. $S_d(G,w)\subseteq S_d(P^\pi_n,w_P)$ (6.15);
--   2. $S_d(G,\chi)\subseteq S_d(P^\pi_n,\chi^{\mathrm{cw}(\pi)})$ for every $\chi\ge1$ (6.16);
--   3. for every ordering $\pi^\star$ of minimum cutwidth, $S_d(G,\chi)\subseteq S_d(P^{\pi^\star}_n,\chi^{\mathrm{cw}(G)})$ (6.17);
--   4. for the fixed ordering $\pi$, the transformation is implemented by at most $\sum_{i=1}^{n-1}|\mathrm{cut}_G(\{v_1,\dots,v_i\})|$ single-edge rerouting steps (Theorem 6.8), and $\sum_{i=1}^{n-1}|\mathrm{cut}_G(\{v_1,\dots,v_i\})|\le(n-1)\,\mathrm{cw}(\pi)$ (6.18).
--
--   Every tensor network state therefore has an MPS representation on the same qudits whose bond dimension is controlled by the cutwidth.
--
--   **Formalization Note** In item 4 the chain of rerouting steps starts at $(G,w)$ and ends at a weighted graph whose edges are edges of $P^\pi_n$, with weights $w_P$; the path edges it lacks have $w_P=1$ (trivial legs, Algorithm 3, line 13). Positions are $0$-based.
--
--   Differences from the source:
--   - reading: (6.18) this transformation can be implemented using at most Σ_i |cut_G({v_1..v_i})| single-edge rerouting steps → a chain of at most that many RerouteStep moves from (G, w) to a weighted graph with edges in P^π_n and weights w_P, path edges absent from it having w_P = 1; reason: the transformation of (6.15) is the passage from (G, w) to (P^π_n, w_P) (Algorithm 3)
--   - reading: (6.17) for an ordering π⋆ of minimum cutwidth → for every ordering π⋆ with cw(π⋆) = cw(G); reason: "an ordering of minimum cutwidth" is any such ordering
--   - reading: If no ordering is given, we can first compute an optimal cutwidth ordering in time 2^{O(cw(G)²)} n → not stated; reason: the sentence reports the algorithm of [TSB05a, TSB05b], which the paper cites and does not prove
--   - encoding: χ in (6.16)–(6.17) → 1 ≤ χ; reason: standing assumption χ ≥ 1 (p.2)
--   - encoding: prefixes {v_1, …, v_i}, i ∈ [n − 1] → {v : π v ≤ j}, j ∈ Fin n with j + 1 < n; reason: 0-based positions
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.11, Eqs. (6.14)–(6.18), p.52; Algorithm 3, p.54

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_wP
import Definitions.Def_AgnosticTNS_Supplement_cwGraph
import Definitions.Def_AgnosticTNS_Supplement_RerouteStep
import Definitions.Def_AgnosticTNS_TNSchi

namespace AgnosticTNS.Supplement

/-- **Theorem 6.11 (Rerouting to an MPS)**, p.52 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Let `G = (V, E)`, `V = [n]`, `w : E → ℕ`, `π : V → [n]` a linear ordering, `v_i = π⁻¹(i)`, `P^π_n` the
labelled path on `v_1, …, v_n` with edge weights `w_P({v_i, v_{i+1}}) = ∏_{e ∈ cut_G({v_1,…,v_i})} w(e)`
(6.14). Then `S_d(G, w) ⊆ S_d(P^π_n, w_P)` (6.15). Consequently `S_d(G, χ) ⊆ S_d(P^π_n, χ^{cw(π)})` (6.16), and
for an ordering `π⋆` of minimum cutwidth `S_d(G, χ) ⊆ S_d(P^{π⋆}_n, χ^{cw(G)})` (6.17). Moreover, for a fixed
ordering `π`, the transformation can be implemented using at most
`Σ_{i=1}^{n−1} |cut_G({v_1,…,v_i})| ≤ (n − 1) cw(π)` (6.18) single-edge rerouting steps.

**Formalization Note** Positions are 0-based: the paper's prefix `{v_1,…,v_i}`, `i ∈ [n − 1]`, is
`{v : π v ≤ j}` with `j = i − 1`, `j + 1 < n`. (6.18): there is a chain of at most that many rerouting
steps (`RerouteStep`, Theorem 6.8) from `(G, w)` to a weighted graph whose edges are edges of `P^π_n`
with weights `w_P`, the path edges it lacks having `w_P = 1` (trivial legs, Algorithm 3 line 13); and the
displayed inequality. The final sentence of the theorem (computing an optimal ordering in time
`2^{O(cw(G)²)} n`) cites [TSB05a, TSB05b] and is not stated. -/
theorem theorem_6_11 (n d : ℕ) (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    (∀ w : G.edgeSet → ℕ, TNS d G w ⊆ TNS d (pathOrd π) (wP G w π)) ∧
    (∀ χ : ℕ, 1 ≤ χ → TNSchi d G χ ⊆ TNSchi d (pathOrd π) (χ ^ cwOrd G π)) ∧
    (∀ χ : ℕ, 1 ≤ χ → ∀ πs : Equiv.Perm (Fin n), cwOrd G πs = cwGraph G →
      TNSchi d G χ ⊆ TNSchi d (pathOrd πs) (χ ^ cwGraph G)) ∧
    (∀ w : G.edgeSet → ℕ, ∃ (k : ℕ) (seq : Fin (k + 1) → Σ H : SimpleGraph (Fin n), H.edgeSet → ℕ),
      k ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val + 1 < n),
        (cut G (Finset.univ.filter fun v => π v ≤ j)).card ∧
      seq 0 = ⟨G, w⟩ ∧ (∀ j : Fin k, RerouteStep (seq j.castSucc) (seq j.succ)) ∧
      (∀ u v, (seq (Fin.last k)).1.Adj u v → (pathOrd π).Adj u v) ∧
      (∀ f : (seq (Fin.last k)).1.edgeSet,
        ∃ h : f.1 ∈ (pathOrd π).edgeSet, (seq (Fin.last k)).2 f = wP G w π ⟨f.1, h⟩) ∧
      (∀ f : (pathOrd π).edgeSet, f.1 ∉ (seq (Fin.last k)).1.edgeSet → wP G w π f = 1)) ∧
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val + 1 < n),
        (cut G (Finset.univ.filter fun v => π v ≤ j)).card ≤ (n - 1) * cwOrd G π := by sorry

end AgnosticTNS.Supplement
