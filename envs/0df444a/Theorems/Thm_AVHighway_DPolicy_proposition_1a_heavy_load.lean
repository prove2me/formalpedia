-- Prove2me | Theorems.Thm_AVHighway_DPolicy_proposition_1a_heavy_load
-- name    : AVHighway.DPolicy.proposition_1a_heavy_load
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:03.861165+00:00
-- url     : https://prove2.me/theorems/9d9f9f83-8b67-491a-ae18-ff7d07da0c06
-- title:
--   Proposition 1(a), p. 16 (corrected: pointwise in p, p ≠ p^(D,W)) — under heavy load, W^D(p) ≤ W^B iff p ≥ p^(D,W)
-- statement:
--   The paper's Proposition 1(a) (p. 16) reads: *There exist $\underline\lambda^{(D,W)}$ and $\bar\lambda^{(D,W)}$ such that for $\lambda \le \underline\lambda^{(D,W)}$, $W^D(p) \ge W^B$ for $p \in [0,1]$; for $\lambda \ge \bar\lambda^{(D,W)}$, $W^D(p) \le W^B$ if and only if $p \ge p^{(D,W)}$.* This item states a corrected form of its heavy-load clause.
--
--   Consider a highway segment of length $L > 0$ with $N \ge 2$ lanes of per-lane capacity $c \ge 1$. The benchmark queue (capacity $Nc$) has speeds $V^B_1 \ge \dots \ge V^B_{Nc} > 0$; under the designated-lane (D) policy the AV queue (one lane, capacity $c$, arrival rate $p\lambda$) has speeds $V^{DA}_1 \ge \dots \ge V^{DA}_c > 0$ and the HV queue ($N-1$ lanes, capacity $(N-1)c$, arrival rate $(1-p)\lambda$) has speeds $V^{DH}_1 \ge \dots \ge V^{DH}_{(N-1)c} > 0$. Assume the jam speeds satisfy
--   $$V^{DH}_{(N-1)c} < V^B_{Nc}, \qquad V^{DH}_{(N-1)c} < V^{DA}_c.$$
--   Let $W^B(\lambda)$ be the benchmark mean travel time and $W^D(p,\lambda) = pW^{DA} + (1-p)W^{DH}$ the D-policy mean travel time, and
--   $$p^{(D,W)} = \frac{V^{DA}_c V^B_{Nc} - V^{DA}_c V^{DH}_{(N-1)c}}{V^{DA}_c V^B_{Nc} - V^B_{Nc} V^{DH}_{(N-1)c}}.$$
--   Then for every AV share $p \in [0,1]$ with $p \ne p^{(D,W)}$ there is $\bar\lambda^{(D,W)}(p) > 0$ such that for all $\lambda \ge \bar\lambda^{(D,W)}(p)$,
--   $$W^D(p,\lambda) \le W^B(\lambda) \iff p \ge p^{(D,W)}.$$
--
--   Under heavy load, then, a designated AV lane reduces mean travel time relative to the no-AV benchmark exactly when the AV share exceeds a threshold determined by the three jam speeds. This is the paper's headline finding on the D policy.
--
--   **Formalization Note** The printed statement is false in two places, and this item corrects it. (i) *One $\bar\lambda$ for all $p$*: $W^D - W^B = G(p) + K/\lambda + o(1/\lambda)$ with $G$ affine and $G(p^{(D,W)}) = 0$, so for every $\lambda$ some $p$ near $p^{(D,W)}$ breaks the equivalence. For instance, with $N = c = 2$, $L = 1$, $V^B = (10, 8, 6, 4)$, $V^{DA} = (10, 9)$, $V^{DH} = (6, 3)$ one has $p^{(D,W)} = 3/8$, and at $p = 3/8 + 10^{-k}$, $\lambda = 10^k$ ($k = 3,\dots,6$) $W^D > W^B$ although $p \ge p^{(D,W)}$; at $p = p^{(D,W)}$ itself $W^D > W^B$ for all those $\lambda$. Hence the threshold $\bar\lambda^{(D,W)}(p)$ depends on $p$, as in the paper's own proof, and $p = p^{(D,W)}$ is excluded. (ii) *The light-load clause* is dropped: at $p = 1$ in the same example, $W^D < W^B$ for every $\lambda > 0$ tested (from $0.01$ to $1000$); the paper's calibrated model behaves the same way. The hypothesis $V^{DH}_{(N-1)c} < V^B_{Nc}$ is the paper's standing assumption (p. 13); $V^{DH}_{(N-1)c} < V^{DA}_c$ is the strict form of the proof's "$V^{DH}_{(N-1)c} - V^{DA}_c \le 0$", needed for $p^{(D,W)}$ to be defined. "Decreasing" speeds are read as nonincreasing.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), Proposition 1(a), p. 16 (heavy-load clause, corrected); proof Online Appendix p. 6; jam-speed assumption p. 13

import Mathlib
import Definitions.Def_AVHighway_DPolicy_Setting

namespace AVHighway.DPolicy
theorem proposition_1a_heavy_load (N c : ℕ) (hN : 2 ≤ N) (hc : 1 ≤ c) (L : ℝ) (hL : 0 < L)
    (VB VDA VDH : ℕ → ℝ)
    (hVB : ∀ n, 1 ≤ n → n ≤ N * c → 0 < VB n) (hVB_anti : AntitoneOn VB (Set.Icc 1 (N * c)))
    (hVDA : ∀ n, 1 ≤ n → n ≤ c → 0 < VDA n) (hVDA_anti : AntitoneOn VDA (Set.Icc 1 c))
    (hVDH : ∀ n, 1 ≤ n → n ≤ (N - 1) * c → 0 < VDH n)
    (hVDH_anti : AntitoneOn VDH (Set.Icc 1 ((N - 1) * c)))
    (hjam : VDH ((N - 1) * c) < VB (N * c))
    (hAV : VDH ((N - 1) * c) < VDA c)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hp_ne : p ≠ pDW N c VB VDA VDH) :
    ∃ lamBar : ℝ, 0 < lamBar ∧ ∀ lam ≥ lamBar,
      (dPolicyW L N c VDA VDH p lam ≤ benchmarkW L N c VB lam ↔ pDW N c VB VDA VDH ≤ p) := by sorry
end AVHighway.DPolicy
