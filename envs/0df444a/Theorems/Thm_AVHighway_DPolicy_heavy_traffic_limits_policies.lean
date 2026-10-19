-- Prove2me | Theorems.Thm_AVHighway_DPolicy_heavy_traffic_limits_policies
-- name    : AVHighway.DPolicy.heavy_traffic_limits_policies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:58.976984+00:00
-- url     : https://prove2.me/theorems/df29e57f-4515-4a1d-ab63-f32ece28984c
-- title:
--   Proof of Proposition 1(a), Online Appendix p. 6 — W^B_∞ = L/V^B_Nc and W^D_∞(p) = (pL)/V^DA_c + [(1 − p)L]/V^DH_(N−1)c
-- statement:
--   Consider a highway segment of length $L > 0$ with $N \ge 2$ lanes of per-lane capacity $c \ge 1$, benchmark speeds $V^B_1, \dots, V^B_{Nc} > 0$, AV-queue speeds $V^{DA}_1, \dots, V^{DA}_c > 0$ and HV-queue speeds $V^{DH}_1, \dots, V^{DH}_{(N-1)c} > 0$, and let $p \in [0,1]$ be the fraction of AVs. As the arrival rate $\lambda \to \infty$,
--   $$W^B(\lambda) \to W^B_\infty = \frac{L}{V^B_{Nc}}, \qquad W^D(p,\lambda) \to W^D_\infty(p) = p\,W^{DA}_\infty + (1-p)\,W^{DH}_\infty = \frac{pL}{V^{DA}_c} + \frac{(1-p)L}{V^{DH}_{(N-1)c}}.$$
--
--   Here $W^B$ is the benchmark mean travel time and $W^D = pW^{DA} + (1-p)W^{DH}$ the mean travel time under the designated-lane policy, whose AV queue receives arrival rate $p\lambda$ and HV queue $(1-p)\lambda$. The heavy-load comparison of the two policies reduces to comparing these two limits.
--
--   **Formalization Note** At $p = 0$ (resp. $p = 1$) the AV (resp. HV) term has weight $0$, and the corresponding limit term $pL/V^{DA}_c$ (resp. $(1-p)L/V^{DH}_{(N-1)c}$) is $0$ as well. Monotonicity of the speeds is not needed and not assumed.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), proof of Proposition 1(a), Online Appendix p. 6, 'In terms of our queueing models, we have W^B_∞ = L/V^B_Nc, …'

import Mathlib
import Definitions.Def_AVHighway_DPolicy_Setting

namespace AVHighway.DPolicy
theorem heavy_traffic_limits_policies (N c : ℕ) (hN : 2 ≤ N) (hc : 1 ≤ c) (L : ℝ) (hL : 0 < L)
    (VB VDA VDH : ℕ → ℝ)
    (hVB : ∀ n, 1 ≤ n → n ≤ N * c → 0 < VB n)
    (hVDA : ∀ n, 1 ≤ n → n ≤ c → 0 < VDA n)
    (hVDH : ∀ n, 1 ≤ n → n ≤ (N - 1) * c → 0 < VDH n)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto (benchmarkW L N c VB) Filter.atTop (nhds (L / VB (N * c))) ∧
      Filter.Tendsto (dPolicyW L N c VDA VDH p) Filter.atTop
        (nhds (p * L / VDA c + (1 - p) * L / VDH ((N - 1) * c))) := by sorry
end AVHighway.DPolicy
