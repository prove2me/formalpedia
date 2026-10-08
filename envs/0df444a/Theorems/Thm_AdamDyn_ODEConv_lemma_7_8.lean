-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_lemma_7_8
-- name    : AdamDyn.ODEConv.lemma_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:14.363993+00:00
-- url     : https://prove2.me/theorems/b94184a7-9b23-452a-a919-7fe7dadcbe4a
-- title:
--   Lemma 7.8 — lower bounds on the $v$-component of solutions of (ODE$_\infty$) and (ODE$_\eta$)
-- statement:
--   Under Assumptions 2.3, 2.4, 7.1 and 7.2, with $0 < b \le 4a$ and $\varepsilon > 0$. For $K \subset \mathcal Z_+$ let $v_{\min}(K) = \inf\{v_i : (x,m,v) \in K,\ i \in \{1,\dots,d\}\}$.
--
--   1. For every compact set $K \subset \mathcal Z_+$ there exists $c > 0$ such that every $z = (x, m, v) \in Z^\infty_\infty(K)$ satisfies
--   $$ v_i(t) \ge c \min\Big(1, \frac{v_{\min}(K)}{2c} + t\Big) \qquad (\forall t \ge 0,\ \forall i).$$
--   2. For every $z_0 \in \mathcal Z_0$ there exists $c > 0$ such that for every $\eta \in [0, +\infty)$ and every $z \in Z^\eta_\infty(z_0)$,
--   $$ v_i(t) \ge c \min(1, t) \qquad (\forall t \ge 0,\ \forall i).$$
--
--   These bounds keep the trajectories away from the boundary $v = 0$ of $\mathcal Z_+$, where $h_\infty$ fails to be Lipschitz.
--
--   **Formalization Note** The lemma's sentence lists only Assumptions 2.3, 2.4, 7.1, 7.2; its proof invokes Propositions 7.6 and 7.7, which assume $0 < b \le 4a$, so this condition is added. The page writes "$v_k$" in the definition of $v_{\min}$; the index is $i$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 14, definition of v_min and Lemma 7.8

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField

open Filter Topology
open scoped ENNReal

namespace AdamDyn.ODEConv

/-- Lemma 7.8 (Barakat & Bianchi, arXiv:1810.02263v4, p. 14). Under Assumptions 2.3, 2.4, 7.1
and 7.2 (and `0 < b ≤ 4a`, which the proof uses through Propositions 7.6 and 7.7):
i) for every compact `K ⊂ 𝒵₊` there is `c > 0` such that every `z ∈ Z^∞_∞(K)` satisfies
`vᵢ(t) ≥ c min(1, v_min(K)/(2c) + t)` for all `t ≥ 0` and all `i`;
ii) for every `z0 ∈ 𝒵₀` there is `c > 0` such that for every `η ∈ [0, +∞)` and every
`z ∈ Z^η_∞(z0)`, `vᵢ(t) ≥ c min(1, t)` for all `t ≥ 0` and all `i`. -/
theorem lemma_7_8 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε) :
    (∀ K : Set (AdamDyn.WellPosed.State d), IsCompact K → (∀ w ∈ K, ∀ i, 0 ≤ w.2.2 i) →
      ∃ c : ℝ, 0 < c ∧ ∀ z0 ∈ K, ∀ z : ℝ → AdamDyn.WellPosed.State d, IsSolutionInf a b ε F S ⊤ z0 z →
        ∀ t : ℝ, 0 ≤ t → ∀ i, c * min 1 (vmin K / (2 * c) + t) ≤ (z t).2.2 i) ∧
    (∀ x0 : AdamDyn.WellPosed.Vec d, ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 ≤ η → ∀ z : ℝ → AdamDyn.WellPosed.State d,
        IsSolutionEta a b ε F S η ⊤ (x0, 0, 0) z →
          ∀ t : ℝ, 0 ≤ t → ∀ i, c * min 1 t ≤ (z t).2.2 i) := by sorry

end AdamDyn.ODEConv
