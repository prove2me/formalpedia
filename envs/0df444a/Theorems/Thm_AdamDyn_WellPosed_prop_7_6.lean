-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_prop_7_6
-- name    : AdamDyn.WellPosed.prop_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:32.410705+00:00
-- url     : https://prove2.me/theorems/aac83bbf-3f7f-4cf1-881d-e4d299025fc5
-- title:
--   Proposition 7.6 — the debiased solutions of $(\mathrm{ODE}_\eta)$ from $(x_0,0,0)$ stay in one compact set, and $F(x(t)) \le F(x_0)$
-- statement:
--   Let $a, \varepsilon > 0$ and $0 < b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1) and coercive, i.e. $F(x) \to +\infty$ as $\|x\| \to \infty$ (Assumption 2.3). Let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz (Assumption 7.2) with $S(x) > 0$ coordinatewise for every $x$ (Assumption 2.4). Fix $x_0 \in \mathbb R^d$ and $z_0 = (x_0, 0, 0) \in \mathcal Z_0$. Then:
--
--   1. There exists a compact set $K \subset \mathcal Z_+$ such that for every $\eta \in [0,+\infty)$, every $T \in (0,+\infty]$ and every solution $z \in Z^\eta_T(z_0)$ of $\dot z(t) = h(t+\eta, z(t))$,
--   $$\{\bar e(t+\eta, z(t)) : t \in (0,T)\} \subset K .$$
--   2. For every such $\eta$, $T$ and $z(t) = (x(t), m(t), v(t))$,
--   $$F(x(t)) \le F(x_0) \qquad \text{for all } t \in [0,T).$$
--
--   The compact set does not depend on $\eta$, $T$ or the solution. Point 1 gives the uniform bounds that make the regularized solutions global and equicontinuous; point 2 is the cost-decrease property (3.6) of Adam near the origin.
--
--   **Formalization Note.** $\bar e(t,z) = (x, m/(1-e^{-at}), v/(1-e^{-bt}))$ is the debiasing map; every $z_0 \in \mathcal Z_0$ is of the form $(x_0,0,0)$, so the statement quantifies over $x_0$. Coercivity is `Tendsto F (cocompact ℝ^d) atTop`.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 13, Proposition 7.6 (and Eq. (3.6), p. 5)

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField
import Definitions.Def_AdamDyn_WellPosed_lyapunov

open scoped NNReal
open Filter

namespace AdamDyn.WellPosed

/-- Proposition 7.6 (p. 13). Under Assumptions 2.3, 2.4, 7.1, 7.2 and `0 < b ≤ 4a`: for every
`z0 = (x0, 0, 0) ∈ 𝒵₀` there is a compact `K ⊂ 𝒵₊` with `ē(t + η, z(t)) ∈ K` for all `η ∈ [0, +∞)`,
`T ∈ (0, +∞]`, `z ∈ Z^η_T(z0)`, `t ∈ (0, T)`; moreover `F(x(t)) ≤ F(x0)` for all `t ∈ [0, T)`. -/
theorem prop_7_6 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hcoer : Tendsto F (cocompact (Vec d)) atTop)
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (x0 : Vec d) :
    (∃ K : Set (State d), IsCompact K ∧ K ⊆ Zplus ∧
      ∀ (η : ℝ≥0) (T : WithTop ℝ), 0 < T → ∀ z : ℝ → State d,
        IsSolutionOn a b ε F S (η : WithTop ℝ≥0) T (x0, 0, 0) z →
          ∀ t ∈ timeIoo T, AdamDyn.ODEConv.ebar a b (t + η) (z t) ∈ K) ∧
    (∀ (η : ℝ≥0) (T : WithTop ℝ), 0 < T → ∀ z : ℝ → State d,
        IsSolutionOn a b ε F S (η : WithTop ℝ≥0) T (x0, 0, 0) z →
          ∀ t ∈ timeIco T, F (z t).1 ≤ F x0) := by sorry

end AdamDyn.WellPosed
