-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_proposition_7_6
-- name    : AdamDyn.ConstStep.proposition_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:43.549083+00:00
-- url     : https://prove2.me/theorems/bb1a3d66-a9be-4594-826d-673b25e27dfc
-- title:
--   Proposition 7.6 — $\bar e(t+\eta,z(t))$ stays in one compact $K\subset\mathcal Z_+$ and $F(x(t))\le F(x_0)$
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be continuously differentiable and coercive with locally Lipschitz gradient, let $S:\mathbb R^d\to\mathbb R^d$ be locally Lipschitz with $S(x)>0$ coordinatewise for every $x$ (Assumptions 2.3, 2.4, 7.1, 7.2), and let $\varepsilon>0$ and $0<b\le 4a$. Fix $x_0\in\mathbb R^d$ and $z_0=(x_0,0,0)$. Then:
--
--   1. there is a compact set $K\subset\mathcal Z_+$ such that for all $\eta\in[0,+\infty)$, all $T\in(0,+\infty]$ and all solutions $z\in Z^\eta_T(z_0)$ of $\dot z(t)=h(t+\eta,z(t))$ on $[0,T)$,
--
--   $$
--   \{\bar e(t+\eta,z(t)) : t\in(0,T)\}\subset K ;
--   $$
--
--   2. writing $z(t)=(x(t),m(t),v(t))$ for any such solution, $F(x(t))\le F(x_0)$ for all $t\in[0,T)$.
--
--   In the constant-step analysis this gives the finite radius $R_0=\sup_{t>0}\|\bar e(t,z(t))\|$ used to truncate the iterates.
--
--   **Formalization Note** This deterministic statement is posed for any $F$, $S$ satisfying the hypotheses above, the generality of §7 of the paper; the $F$, $S$ of (2.2) satisfy them under Assumptions 2.2–2.4. $T\in(0,+\infty]$ is an extended nonnegative real and $[0,T)$ is $\{t\ge0 : t<T\}$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 13, Proposition 7.6

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_adamField

open Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Proposition 7.6 (p. 13), for any `F`, `S` satisfying Assumptions 2.3, 2.4, 7.1, 7.2 and
`0 < b ≤ 4a`: for `z0 = (x0, 0, 0) ∈ 𝒵₀` there is a compact `K ⊂ 𝒵₊` such that for all
`η ∈ [0, +∞)`, `T ∈ (0, +∞]` and `z ∈ Z^η_T(z0)`, `ē(t + η, z(t)) ∈ K` for `t ∈ (0, T)`;
moreover `F(x(t)) ≤ F(x0)` for all `t ∈ [0, T)`. -/
theorem proposition_7_6 {d : ℕ} (F : E d → ℝ) (S : E d → E d) (a b ε : ℝ) (x0 : E d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (E d)) atTop)
    (ha : 0 < a) (hb : 0 < b) (hab : b ≤ 4 * a) (hε : 0 < ε) :
    (∃ K : Set (Z d), IsCompact K ∧ (∀ w ∈ K, InZplus w) ∧
      ∀ η : ℝ, 0 ≤ η → ∀ T : ℝ≥0∞, 0 < T → ∀ z : ℝ → Z d,
        IsSolutionOn a b ε F S η T (x0, 0, 0) z →
        ∀ t : ℝ, 0 < t → ENNReal.ofReal t < T → AdamDyn.ODEConv.ebar a b (t + η) (z t) ∈ K) ∧
    (∀ η : ℝ, 0 ≤ η → ∀ T : ℝ≥0∞, 0 < T → ∀ z : ℝ → Z d,
        IsSolutionOn a b ε F S η T (x0, 0, 0) z →
        ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < T → F (z t).1 ≤ F x0) := by sorry

end AdamDyn.ConstStep
