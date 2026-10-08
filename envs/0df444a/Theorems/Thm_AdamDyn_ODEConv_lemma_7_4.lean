-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_lemma_7_4
-- name    : AdamDyn.ODEConv.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:24.527448+00:00
-- url     : https://prove2.me/theorems/11e14c64-814d-4004-b4cf-2f4aa0c88b02
-- title:
--   Lemma 7.4 — solutions of (ODE$_\eta$) started in $\mathcal Z_+$ stay in $\mathcal Z_+^*$ for positive times
-- statement:
--   Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz with $S(x) > 0$ coordinatewise for every $x$ (Assumptions 7.2 and 2.4). Let $a, b, \varepsilon > 0$.
--
--   For every $\eta \in [0, +\infty]$, every $T \in (0, +\infty]$, every initial condition $z_0 \in \mathcal Z_+$ and every solution $z = (x, m, v) \in Z^\eta_T(z_0)$ of $\dot z(t) = h(t+\eta, z(t))$ (of $\dot z = h_\infty(z)$ when $\eta = +\infty$) on $[0,T)$,
--   $$ z\big((0, T)\big) \subset \mathcal Z_+^*, \qquad\text{i.e. } v_i(t) > 0 \text{ for all } t \in (0,T),\ i \in \{1,\dots,d\}. $$
--
--   This positivity is what makes $V$, $V_\infty$ and $W_\delta$ differentiable along trajectories.
--
--   **Formalization Note** The two conjuncts are the cases $\eta \in [0,+\infty)$ and $\eta = +\infty$. The constants $a, b > 0$ (Assumption 2.5) and $\varepsilon > 0$ (Algorithm 2.1) are standing assumptions of the paper and are stated as hypotheses.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 12, Lemma 7.4

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField

open scoped ENNReal

namespace AdamDyn.ODEConv

/-- Lemma 7.4 (Barakat & Bianchi, arXiv:1810.02263v4, p. 12). Let Assumptions 2.4, 7.1 and 7.2
hold. For every `η ∈ [0, +∞]`, `T ∈ (0, +∞]`, `z0 ∈ 𝒵₊`, `z ∈ Z^η_T(z0)`, it holds that
`z((0, T)) ⊂ 𝒵₊*`. The first conjunct is the case `η ∈ [0, +∞)`, the second the case `η = +∞`
(the autonomous field `h∞`). -/
theorem lemma_7_4 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    (∀ η : ℝ, 0 ≤ η → ∀ T : ℝ≥0∞, 0 < T → ∀ z0 : AdamDyn.WellPosed.State d, (∀ i, 0 ≤ z0.2.2 i) →
      ∀ z : ℝ → AdamDyn.WellPosed.State d, IsSolutionEta a b ε F S η T z0 z →
        ∀ t ∈ timeIoo T, InZplusStar (z t)) ∧
    (∀ T : ℝ≥0∞, 0 < T → ∀ z0 : AdamDyn.WellPosed.State d, (∀ i, 0 ≤ z0.2.2 i) →
      ∀ z : ℝ → AdamDyn.WellPosed.State d, IsSolutionInf a b ε F S T z0 z →
        ∀ t ∈ timeIoo T, InZplusStar (z t)) := by sorry

end AdamDyn.ODEConv
