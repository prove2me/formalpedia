-- Prove2me | Theorems.Thm_EngageInfo_concave_closure_segments
-- name    : EngageInfo.concave_closure_segments
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:28.91043+00:00
-- url     : https://prove2.me/theorems/26d66bfc-bd3c-431f-9fe6-8cfa0f1a235d
-- title:
--   §3.2 — $V^*$ is the segment AD, the segments ABD, or the segments ABCD
-- statement:
--   Assume $\alpha_1<\alpha_{\bar e}$ and write $m=\max\{\alpha_0,\alpha_1\}$, $A=(0,\theta_L-c)$, $B=(m,\theta_L+\bar e-c)$, $C=(\alpha_{\bar e},\theta_L+\bar e-c)$, $D=(1,\theta_H-c)$. For $\alpha\in[0,1]$:
--
--   1. if $\bar e<\alpha_0\Theta$: $V^*(\alpha)=\theta_L-c+\alpha\Theta$ (segment AD), and $v^*(\alpha)<\theta_L-c+\alpha\Theta$ for every $\alpha\in(0,1)$;
--   2. if $\alpha_0\Theta\le\bar e\le\Theta$ (segments ABD):
--   $$V^*(\alpha)=\begin{cases}\theta_L-c+\alpha\bar e/m, & \alpha\in[0,m],\\ \theta_L+\bar e-c+(\alpha-m)\dfrac{\Theta-\bar e}{1-m}, & \alpha\in[m,1];\end{cases}$$
--   3. if $\bar e>\Theta$ (segments ABCD):
--   $$V^*(\alpha)=\begin{cases}\theta_L-c+\alpha\bar e/m, & \alpha\in[0,m],\\ \theta_L+\bar e-c, & \alpha\in[m,\alpha_{\bar e}],\\ \theta_L+\bar e-c+(\alpha-\alpha_{\bar e})\dfrac{\Theta-\bar e}{1-\alpha_{\bar e}}, & \alpha\in[\alpha_{\bar e},1].\end{cases}$$
--
--   These are the optimal value functions drawn in Figure 2; the kinks of $V^*$ are the posteriors of Proposition 1.
--
--   Differences from the source:
--   - encoding: "the line segments ABD" / "ABCD" through the points of Figure 2 → the explicit piecewise-linear formulas through A = (0, θL − c), B = (m, θL + ē − c), C = (α_ē, θL + ē − c), D = (1, θH − c); reason: a segment is the line through its two named endpoints; 0 < m < α_ē < 1, so no denominator vanishes
--   - reading: "the seller's equilibrium expected payoff" v∗(α), with "the equilibrium" called unique (p.8) → v∗(α) = the maximum of the seller's payoffs over all pure subgame-perfect equilibria at belief α (seller-preferred equilibrium); reason: at α ∈ {α₀, α₁, α_ē} the subgame has several SPE with different seller payoffs; the closed interval of Lemma 1 and the values of (6) there are those of the seller-preferred SPE
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §3.2, pp.13–14 (scenario (i) "strictly lower … than the line segment AD", scenario (ii) "line segments ABD", scenario (iii) "ABCD"), with Figure 2, p.11

import Mathlib
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Definitions.Def_EngageInfo_concaveClosure

namespace EngageInfo

/-- **The optimal value function V* in the three scenarios (segments AD, ABD, ABCD).**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §3.2, pp.13–14, with
Figure 2, p.11: "Scenario (i) captures the case ē < α₀Θ such that v∗ is strictly lower, for any
α ∈ (0, 1), than the line segment AD connecting the two extreme points of v∗"; "as demonstrated in
scenario (ii) for intermediate ē, the optimal value function V∗(α) would be captured by the line
segments ABD"; "imperfect information would be optimal in scenario (iii) for large ē, where the line
segments to represent the optimal value function V∗(α) become ABCD".

With `A = (0, θ_L − c)`, `B = (m, θ_L + ē − c)`, `C = (α_ē, θ_L + ē − c)`, `D = (1, θ_H − c)` and
`m = max{α₀, α₁}`, assume `α₁ < α_ē`. For `α ∈ [0, 1]`:
1. if `ē < α₀Θ`: `V*(α) = θ_L − c + αΘ` (segment AD), and `v*(α) < θ_L − c + αΘ` for `α ∈ (0, 1)`;
2. if `α₀Θ ≤ ē ≤ Θ`: `V*(α) = θ_L − c + αē/m` on `[0, m]` and
   `V*(α) = θ_L + ē − c + (α − m)(Θ − ē)/(1 − m)` on `[m, 1]` (ABD);
3. if `ē > Θ`: `V*(α) = θ_L − c + αē/m` on `[0, m]`, `V*(α) = θ_L + ē − c` on `[m, α_ē]`, and
   `V*(α) = θ_L + ē − c + (α − α_ē)(Θ − ē)/(1 − α_ē)` on `[α_ē, 1]` (ABCD).

**Formalization Note** `0 < α₀ ≤ m < α_ē < 1` under the hypotheses, so no denominator vanishes. -/
theorem concave_closure_segments (M : Params) (hα : M.α₁ < M.αbar) :
    (M.ebar < M.α₀ * M.Θ →
      (∀ α ∈ Set.Icc (0 : ℝ) 1, concaveClosure (vstar M) α = M.θL - M.c + α * M.Θ) ∧
      ∀ α ∈ Set.Ioo (0 : ℝ) 1, vstar M α < M.θL - M.c + α * M.Θ) ∧
    (M.α₀ * M.Θ ≤ M.ebar ∧ M.ebar ≤ M.Θ →
      (∀ α ∈ Set.Icc (0 : ℝ) M.m, concaveClosure (vstar M) α = M.θL - M.c + α * M.ebar / M.m) ∧
      ∀ α ∈ Set.Icc M.m 1, concaveClosure (vstar M) α =
        M.θL + M.ebar - M.c + (α - M.m) * (M.Θ - M.ebar) / (1 - M.m)) ∧
    (M.Θ < M.ebar →
      (∀ α ∈ Set.Icc (0 : ℝ) M.m, concaveClosure (vstar M) α = M.θL - M.c + α * M.ebar / M.m) ∧
      (∀ α ∈ Set.Icc M.m M.αbar, concaveClosure (vstar M) α = M.θL + M.ebar - M.c) ∧
      ∀ α ∈ Set.Icc M.αbar 1, concaveClosure (vstar M) α =
        M.θL + M.ebar - M.c + (α - M.αbar) * (M.Θ - M.ebar) / (1 - M.αbar)) := by sorry

end EngageInfo
