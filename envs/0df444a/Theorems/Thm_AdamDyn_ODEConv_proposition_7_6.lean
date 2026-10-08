-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_proposition_7_6
-- name    : AdamDyn.ODEConv.proposition_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:54.55675+00:00
-- url     : https://prove2.me/theorems/ca378758-db28-4d41-9d13-f240228de856
-- title:
--   Proposition 7.6 — debiased solutions of (ODE$_\eta$) from $(x_0,0,0)$ stay in a compact set, and $F(x(t)) \le F(x_0)$
-- statement:
--   Let $F$ be continuously differentiable with locally Lipschitz gradient and coercive (Assumptions 7.1, 2.3); let $S$ be locally Lipschitz with $S(x) > 0$ for all $x$ (Assumptions 7.2, 2.4). Assume $0 < b \le 4a$ and $\varepsilon > 0$.
--
--   For every $z_0 = (x_0, 0, 0) \in \mathcal Z_0$ there exists a compact set $K \subset \mathcal Z_+$ such that, for all $\eta \in [0, +\infty)$, all $T \in (0, +\infty]$ and all $z = (x, m, v) \in Z^\eta_T(z_0)$,
--   $$\{ \bar e(t + \eta, z(t)) : t \in (0, T) \} \subset K, \qquad F(x(t)) \le F(x_0) \ \text{ for all } t \in [0, T).$$
--
--   The compact $K$ depends on $x_0$ only, not on $\eta$, $T$ or the solution; this uniformity is what yields boundedness of the (ODE) trajectory and of its debiased moments.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 13, Proposition 7.6

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField

open Filter Topology
open scoped ENNReal

namespace AdamDyn.ODEConv

/-- Proposition 7.6 (Barakat & Bianchi, arXiv:1810.02263v4, p. 13). Let Assumptions 2.3, 2.4,
7.1 and 7.2 hold and `0 < b ≤ 4a`. For every `z0 = (x0, 0, 0) ∈ 𝒵₀` there is a compact
`K ⊂ 𝒵₊` such that for all `η ∈ [0, +∞)`, all `T ∈ (0, +∞]` and all `z ∈ Z^η_T(z0)`,
`{ē(t + η, z(t)) : t ∈ (0, T)} ⊂ K`; moreover `F(x(t)) ≤ F(x0)` for all `t ∈ [0, T)`. -/
theorem proposition_7_6 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε) (x0 : AdamDyn.WellPosed.Vec d) :
    ∃ K : Set (AdamDyn.WellPosed.State d), IsCompact K ∧ (∀ w ∈ K, ∀ i, 0 ≤ w.2.2 i) ∧
      ∀ η : ℝ, 0 ≤ η → ∀ T : ℝ≥0∞, 0 < T → ∀ z : ℝ → AdamDyn.WellPosed.State d,
        IsSolutionEta a b ε F S η T (x0, 0, 0) z →
          (∀ t ∈ timeIoo T, ebar a b (t + η) (z t) ∈ K) ∧
            ∀ t ∈ timeIco T, F (z t).1 ≤ F x0 := by sorry

end AdamDyn.ODEConv
