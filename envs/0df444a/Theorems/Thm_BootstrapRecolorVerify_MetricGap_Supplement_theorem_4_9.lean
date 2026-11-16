-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_Supplement_theorem_4_9
-- name    : BootstrapRecolorVerify.MetricGap.Supplement.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:33:18.537518+00:00
-- url     : https://prove2.me/theorems/edd6f762-b54e-49b6-9b8f-5ab069fbf387
-- title:
--   Theorem 4.9 — All-stage monochromatic proxy lower bound
-- statement:
--   For every fixed integer $r\ge2$ and every sufficiently large even $n$, every Part I matching history satisfying §4.1's cloud expansion and local sparsity has the following property simultaneously for every $1\le i\le r$: the constant
--
--   $$c_i=\frac1{2\cdot180^{i-1}i!}>0$$
--
--   depends only on $i$, and every level-$i$ monochromatic map $\varphi_i:V(G_i)\to V(G_i)$ satisfies
--
--   $$\overline{\operatorname{cost}}_i(\varphi_i)\ge c_iL^{1-\eta}.$$
--
--   The source's full normalized proxy cost is used: earlier-level edge costs and the pendant contribution at every stage, together with the uncapped terminal-distance term on level-$r$ edges at the final stage. The hard cap is $\rho_i=\min(d_i,L^{2-\eta i})$. The same fixed sequence works for every recursion depth, graph size, matching history and coloring. This companion theorem gives Part I's deterministic lower bound.
--
--   Differences from the source:
--   - encoding: fixed r≥2 and sufficiently large even n under the Part I construction → one threshold n₀(r)≥2 preceding every even n and every matching history; reason: this spells out the standing assumptions on pp.5–6 without excluding any sufficiently large even n
--   - generalization: some positive c_i depending only on i → the explicit sequence c_i=1/(2·180^(i−1)·i!), with positivity in the conclusion; reason: a named positive sequence depending only on i is stronger than its existence and implies it; pp.13,15 choose c₁=1/2 and c_i=c_(i−1)/(180i)
--   - encoding: the standing expansion/local sparsity properties and finite proxy costs → GoodHistory and extended nonnegative proxy costs, with i=k+1; reason: GoodHistory contains precisely the two standing graph properties; these imply connectivity, so the extended costs equal the real source costs at every theorem input; every stage 1≤i≤r occurs
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Theorem 4.9, p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=12; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Proxy

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- Theorem 4.9 p.12, including ALL stages and the top-stage proxy cost.
The fixed sequence c_i is the explicit choice in the proof, pp.13,15.
GoodHistory contains expansion and local sparsity only. -/
theorem theorem_4_9 :
    ∀ r : ℕ, 2 ≤ r → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n → ∀ H : History n r, GoodHistory H →
        ∀ k : ℕ, ∀ h : k + 1 ≤ r,
          0 < lowerConstant (k + 1) ∧
          ∀ f : Vertex n (k + 1) → Vertex n (k + 1), Monochromatic f →
            ENNReal.ofReal (lowerConstant (k + 1) * Real.rpow (lengthScale r n) (1 - eta r)) ≤
              proxyCost r (historyPrefix n (k + 1) h H) (by omega) f := by sorry

end BootstrapRecolorVerify.MetricGap.Supplement
