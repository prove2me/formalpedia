-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_proposition_7_17
-- name    : AdamDyn.ODEConv.proposition_7_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:29.696739+00:00
-- url     : https://prove2.me/theorems/8524238d-dd4e-4b5d-8a9a-44e9ba9c623e
-- title:
--   Proposition 7.17 (APT) — the solution of (ODE) from $(x_0,0,0)$ is an asymptotic pseudotrajectory of $\Phi$
-- statement:
--   Under Assumptions 2.3, 2.4, 7.1 and 7.2, with $0 < b \le 4a$ and $\varepsilon > 0$, let $\Phi$ be the semiflow (7.8) of $(\mathrm{ODE}_\infty)$ on $\mathcal Z_+$. For every $x_0 \in \mathbb R^d$ and every global solution $z$ of (ODE) with initial condition $(x_0, 0, 0)$, $z$ is an asymptotic pseudotrajectory of $\Phi$: for every $T > 0$,
--   $$ \lim_{t \to \infty} \sup_{s \in [0, T]} d\big(z(t+s), \Phi_s(z(t))\big) = 0 .$$
--
--   The non-autonomous Adam trajectory therefore shadows the autonomous system over every bounded time window, asymptotically.
--
--   **Formalization Note** The solution is restricted to $[0,+\infty)$ and viewed in $\mathcal Z_+$ through $(x,m,v) \mapsto (x,m,|v|)$, which is the identity on its values. Distances use Mathlib's product metric (max of the three Euclidean distances), uniformly equivalent to the Euclidean metric on $\mathbb R^{3d}$, so the APT property is the paper's.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 19, Proposition 7.17

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory

open Filter Topology
open scoped NNReal

namespace AdamDyn.ODEConv

/-- Proposition 7.17 (APT) (Barakat & Bianchi, arXiv:1810.02263v4, p. 19). Let Assumptions 2.3,
2.4, 7.1 and 7.2 hold and `0 < b ≤ 4a`. For every `z0 = (x0, 0, 0) ∈ 𝒵₀`, the global solution
`Z^0_∞(z0)` of (ODE) is an asymptotic pseudotrajectory of the semiflow `Φ` of (7.8). The solution
is taken on `[0, +∞)` and viewed in `𝒵₊` (where it takes its values) through `toZplus`. -/
theorem proposition_7_17 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (Φ : Flow ℝ≥0 (Zplus d)) (hΦ : IsODEInfSemiflow a b ε F S Φ)
    (x0 : AdamDyn.WellPosed.Vec d) (z : ℝ → AdamDyn.WellPosed.State d) (hz : IsGlobalSolution a b ε F S x0 z) :
    StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ
      (fun t : ℝ≥0 => toZplus (z t)) := by sorry

end AdamDyn.ODEConv
