-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_Supplement_theorem_4_2
-- name    : ApproxEquilibriumCost.General.Supplement.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:00.699655+00:00
-- url     : https://prove2.me/theorems/5756f9e1-39c2-46bb-9b9f-b492a5df69c1
-- title:
--   Theorem 4.2 (companion theorem; not used in the proof of the goal) — three-regime polynomial cost upper bound
-- statement:
--   Consider any finite nonatomic congestion game with positive real demands and polynomial resource latencies of degree at most an integer $d\ge1$, with nonnegative coefficients. Let $f$ be a Nash equilibrium with $C(f)>0$. For every real $\epsilon\ge0$ and every $\epsilon$-equilibrium $f'$ for the same game, all three implications hold:
--
--   $$\begin{aligned}
--   0\le\epsilon\le\epsilon_1(d)&\implies\frac{C(f')}{C(f)}\le1+\omega_d\!\left(\frac{\epsilon}{1+\epsilon}\right),\\
--   \epsilon_1(d)\le\epsilon\le\epsilon_2(d)&\implies\frac{C(f')}{C(f)}\le\left(\frac1{1+\epsilon}-c_d\right)^{-1},\\
--   \epsilon\ge\epsilon_2(d)&\implies\frac{C(f')}{C(f)}\le(1+\epsilon)^{d+1}.
--   \end{aligned}$$
--
--   The inverse $\omega_d$, constant $c_d$ and thresholds are those of Definition 4.1. Both adjacent bounds apply at each shared endpoint. This companion theorem bounds cost increases in general polynomial games, independently of the proof of the retained lower-bound goal.
--
--   Differences from the source:
--   - encoding: arbitrary finite resources and populations, subset strategies and real flows → the published Game n k and its bijective route enumeration; reason: finite relabelling preserves all source instances, empty subset strategies and real traffic amounts
--   - encoding: latencies defined on nonnegative reals → total real functions satisfying the published Game fields on [0,∞); reason: every evaluated load is nonnegative by feasibility
--   - encoding: integer degree d ≥ 1 and real fractional powers → natural d with 1 ≤ d and Real.rpow with real quotients; reason: the degree domain and all source-domain power values coincide
--   - encoding: omega_d is the inverse of lambda_d on [0,1) → omega d y is the infimum of {x ≥ 0 : y ≤ lambda d x}, with zero outside d ≥ 1 and 0 ≤ y < 1; reason: Lemma A.1 identifies this nonempty bounded-below infimum with the unique inverse; epsilon/(1+epsilon) always lies in [0,1) for epsilon ≥ 0
--   - encoding: a piecewise bound with overlapping closed regimes → the conjunction of all three regime implications; reason: both adjacent bounds are asserted at each threshold, exactly as printed
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Theorem 4.2, printed p.17 = PDF p.17 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_PolynomialLatencies
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_UpperParameters

namespace ApproxEquilibriumCost.General.Supplement

/-- Theorem 4.2, printed/PDF p.17, parameters p.16. All three
regimes hold, including both adjacent bounds at each shared endpoint. -/
theorem theorem_4_2 {n k : ℕ} (G : Game n k) (d : ℕ) (hd : 1 ≤ d)
    (hpoly : HasPolynomialLatencies G d) (f : Flow G) (hf : IsNash G f)
    (hcost : 0 < cost G f) (ε : ℝ) (hε : 0 ≤ ε)
    (f' : Flow G) (hf' : IsApproxNash G ε f') :
    (ε ≤ epsilon1 d → cost G f' / cost G f ≤ 1 + omega d (ε / (1 + ε))) ∧
    (epsilon1 d ≤ ε ∧ ε ≤ epsilon2 d →
      cost G f' / cost G f ≤ (1 / (1 + ε) - c d)⁻¹) ∧
    (epsilon2 d ≤ ε → cost G f' / cost G f ≤ (1 + ε) ^ (d + 1)) := by sorry

end ApproxEquilibriumCost.General.Supplement
