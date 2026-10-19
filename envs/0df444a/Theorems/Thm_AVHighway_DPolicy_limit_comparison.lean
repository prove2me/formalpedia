-- Prove2me | Theorems.Thm_AVHighway_DPolicy_limit_comparison
-- name    : AVHighway.DPolicy.limit_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:58.971355+00:00
-- url     : https://prove2.me/theorems/462350c2-92b4-4d6f-b0a4-144ebf2aa657
-- title:
--   Proof of Proposition 1(a), Online Appendix p. 6 — W^D_∞(p) ≤ W^B_∞ if and only if p ≥ p^(D,W)
-- statement:
--   Let $L > 0$ and let the three jam speeds be positive: $V^B_{Nc} > 0$, $V^{DA}_c > 0$, $V^{DH}_{(N-1)c} > 0$, with the AV lane faster when full than the HV lanes, $V^{DH}_{(N-1)c} < V^{DA}_c$. Then for every real $p$,
--   $$\frac{pL}{V^{DA}_c} + \frac{(1-p)L}{V^{DH}_{(N-1)c}} \le \frac{L}{V^B_{Nc}} \iff p \ge p^{(D,W)} = \frac{V^{DA}_c V^B_{Nc} - V^{DA}_c V^{DH}_{(N-1)c}}{V^{DA}_c V^B_{Nc} - V^B_{Nc} V^{DH}_{(N-1)c}}.$$
--
--   The left side is the heavy-traffic travel time $W^D_\infty(p)$ of the designated-lane policy, the right side that of the benchmark, $W^B_\infty$. The statement identifies the AV share above which the designated lane wins under heavy load.
--
--   **Formalization Note** The paper writes "since $V^{DH}_{(N-1)c} - V^{DA}_c \le 0$ the direction of inequality changes"; the inequality is taken strict here, which is necessary: with equality the threshold's denominator vanishes and the equivalence fails. The paper's proof writes the denominator as $V^B_{Nc}V^{DA}_c - V^B_{Nc}V^{DH}_{(N-1)c}$, equal to the statement's; the single definition of $p^{(D,W)}$ uses the statement's form. The equivalence holds for every real $p$, not only $p \in [0,1]$.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), proof of Proposition 1(a), Online Appendix p. 6, 'As a result, W^D_∞(p) ≤ W^B_∞ if and only if p ≥ p^(D,W) …'

import Mathlib
import Definitions.Def_AVHighway_DPolicy_Setting

namespace AVHighway.DPolicy
theorem limit_comparison (N c : ℕ) (L : ℝ) (hL : 0 < L) (VB VDA VDH : ℕ → ℝ)
    (hVBjam : 0 < VB (N * c)) (hVDAjam : 0 < VDA c) (hVDHjam : 0 < VDH ((N - 1) * c))
    (hAV : VDH ((N - 1) * c) < VDA c) (p : ℝ) :
    p * L / VDA c + (1 - p) * L / VDH ((N - 1) * c) ≤ L / VB (N * c) ↔
      pDW N c VB VDA VDH ≤ p := by sorry
end AVHighway.DPolicy
