-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_13
-- name    : DistancePreserver934.Exact.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:27.962716+00:00
-- url     : https://prove2.me/theorems/d6a21492-c5c1-4d2e-903e-b421b1911b1f
-- title:
--   Lemma 13 (dense loyal core) (corrected: $|V_H|>0$)
-- statement:
--   Let $H$ be a minimal distance preserver of $(G,R)$, $R$ a demand set, with $0<|V_H|\le n$ and $|E_H|\le nd$. If
--   $$|\Lambda_H|\ge\frac{nd}{20},$$
--   then there is a nonempty vertex set $V^*\subseteq V_H$ such that the core $H_L=(V^*,\Lambda^*_H)$, with $\Lambda^*_H=\{\{u,v\}\in\Lambda_H:u,v\in V^*\}$ all private edges inside $V^*$, satisfies
--   $$m:=|\Lambda^*_H|\ge\frac{nd}{40},\qquad\deg_{H_L}(x)\ge\frac d{40}\quad(x\in V^*).\tag{6}$$
--
--   The core supplies the rich vertices and loyal edges of the counting arguments of §5.2 and §5.4. Both constants are exactly $1/40$.
--
--   Differences from the source:
--   - correction: hypotheses |V_H| ≤ n, |E_H| ≤ nd, |Λ_H| ≥ nd/20 (no positivity of the graph size) → additionally V_H ≠ ∅ (0 < |V|); reason: the printed statement fails with G = H empty, R = ∅, n = 0, d = 3, l = r = 6: all stated and standing assumptions hold, but no nonempty V* exists and no Q ⊆ R has positive size. Under the source radius condition (5), n > 0 forces V_H ≠ ∅ by the edge and private-mass bounds, so the chosen correction excludes exactly the same source instances as n > 0. For the generalized Lemma 13 after dropping (5), V_H = ∅, n = 1, d = 0 is an additional counterexample to using n > 0 alone; this second example does not satisfy (5). The goal and its empty-graph instance are unchanged
--   - generalization: the §5 standing assumption λ_H(q) ≥ l (Equation (4)) and the radius condition (5) in force → no lower bound on private lengths and no radius parameter assumed; reason: the pruning statement does not involve l or r; the Lean statement applies in particular under (4) and (5)
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 13, printed p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 13 (dense loyal core), printed p.15 / PDF p.16, corrected by requiring `V_H ≠ ∅`.
If `H` is a minimal distance preserver of `(G, R)` with `|V_H| ≤ n`, `|E_H| ≤ nd` and
`|Λ_H| ≥ nd/20`, then some nonempty `V* ⊆ V_H` has induced private-edge set `Λ*_H` with
`|Λ*_H| ≥ nd/40` and `deg_{H_L}(x) ≥ d/40` for every `x ∈ V*` (Equation (6)). -/
theorem lemma_13 {V : Type} [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V))
    (n : ℕ) (d : ℝ)
    (hV0 : 0 < Fintype.card V)
    (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (hV : Fintype.card V ≤ n) (hE : (numEdges H : ℝ) ≤ n * d)
    (hΛ : (n : ℝ) * d / 20 ≤ ((privEdges H R).card : ℝ)) :
    ∃ Vs : Finset V, Eq6 H R Vs n d := by sorry

end DistancePreserver934.Exact
