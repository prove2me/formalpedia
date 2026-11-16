-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_Supplement_induced_round_weight_bound
-- name    : FlowOptimalSeparators.MinorFree.Supplement.induced_round_weight_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:02:14.550241+00:00
-- url     : https://prove2.me/theorems/08a547e1-9a51-4c54-aee5-6d9e33ffa967
-- title:
--   Lemma 6 — Section 5 round vertex-weight norm
-- statement:
--   Let $G$ be $H$-induced-minor-free with $n$ vertices and $m>0$ edges, and run Algorithm 2 (Cluster-FTRL) with $\mu=\iota=1$, a positive number of rounds $T$, and $D=n/\sqrt{mT}$. The round-$t$ vertex weights are
--   $$w_t[v]=1+\frac{n\deg(v)}{2m}+4D\Bigl(q_t[v]+\sum_{u\in N_G(v)}q_t[u]\Bigr),\qquad q_t=\sum_{i<t}p_i,$$
--   where $p_i$ is the load vector of the connector produced in round $i$. For every actual prefix of fewer than $T$ connectors, the weight vector of the next attempted round satisfies
--   $$\|w_t\|_1\le 14n.$$
--   The statement is made for every $D$ with $0<D\le n/\sqrt{mT}$, which contains Section 5's value. It covers the attempted round that returns a separator, and bounds the total integer weight passed to CUTORCLUSTER in the proof of Theorem 3.
--
--   Differences from the source:
--   - encoding: finite simple graphs H and G on arbitrary vertex sets → SimpleGraph (Fin a) and SimpleGraph (Fin n), with |V(H)| = a; reason: vertex relabelling preserves induced minors, paths, components and edge counts
--   - reading: exactly 3n/4 terminals; line 10 chooses them outside the root → ceil(3n/4) terminals, excluding the root whenever enough other cluster vertices exist (published WideConnector and FTRLRound); reason: the printed count is undefined off multiples of four; at n=401 a 301-vertex cluster needs the root to reach 301 terminals; this agrees with the source when four divides n
--   - encoding: the regularization n deg(v)/(2m) in an attempted FTRL round → 0 < m; reason: this excludes only division by zero in the source formula; edgeless inputs need no FTRL rounds
--   - generalization: in every round → the next attempted round after any source-valid prefix of length less than T; reason: every actual prefix is included, and only the preceding legal transitions are used; this includes the last attempted round without assuming a further connector
--   - generalization: T = c(|V(H)| + |E(H)|) and D = n/√(mT) → every natural T > 0 and every real D with 0 < D ≤ n/√(mT); reason: specializes to Section 5's T and D; for each prefix legal at its own D, the transition gives the same weighted-load bound, and mTD² ≤ n² gives the claimed norm estimate without fixing T in terms of H
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 19–20, Lemma 6, Eqs. (28)–(29), Section 5 parameters

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_FTRLTrace
import Definitions.Def_FlowOptimalSeparators_MinorFree_Supplement_InducedMinorFree

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree.Supplement

/-- Lemma 6, p.19 (proof pp.19-20): Section 5's Cluster-FTRL with `µ = ι = 1`. For the next
attempted round after any actual prefix of length `< T`, including an attempt that returns a
separator, `‖w_t‖₁ ≤ 14n`. Stated for every `0 < D ≤ n/√(mT)`, which contains Section 5's
`D = n/√(mT)`. -/
theorem induced_round_weight_bound {a n : ℕ} (H : Graph a) (G : Graph n)
    (hG : InducedMinorFree H G) (hm : 0 < edgeCount G) (T : ℕ) (hT : 0 < T) (D : ℝ)
    (hD : 0 < D) (hDle : D ≤ (n : ℝ) / Real.sqrt ((edgeCount G : ℝ) * T))
    (Cs : List (WideConnector G)) (ht : Cs.length < T)
    (hrun : IsFTRLPrefix G D 1 1 Cs) :
    (∑ v, |roundWeight G D 1 1 Cs v|) ≤ 14 * n := by sorry

end FlowOptimalSeparators.MinorFree.Supplement
