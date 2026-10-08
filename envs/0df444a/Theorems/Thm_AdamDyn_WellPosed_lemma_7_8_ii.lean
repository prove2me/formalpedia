-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_lemma_7_8_ii
-- name    : AdamDyn.WellPosed.lemma_7_8_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:07.760842+00:00
-- url     : https://prove2.me/theorems/88325712-cff4-4788-8553-10517d2c813c
-- title:
--   Lemma 7.8 ii) — $v_i(t) \ge c\min(1,t)$ uniformly over the solutions of $(\mathrm{ODE}_\eta)$ from $(x_0,0,0)$
-- statement:
--   Let $a, \varepsilon > 0$ and $0 < b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1) and coercive (Assumption 2.3), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz (Assumption 7.2) with $S(x) > 0$ coordinatewise (Assumption 2.4). Fix $z_0 = (x_0,0,0) \in \mathcal Z_0$. Then there exists $c > 0$ such that for every $\eta \in [0,+\infty)$ and every global solution $z(t) = (x(t), m(t), v(t))$ in $Z^\eta_\infty(z_0)$,
--   $$v_i(t) \ge c \min(1, t) \qquad \text{for all } t \ge 0 \text{ and all } i \in \{1,\dots,d\}.$$
--
--   The second-moment variable leaves $0$ at least linearly, uniformly in the regularization parameter $\eta$; this controls the singularity of $h$ at $v = 0$ in the passage to the limit $\eta \downarrow 0$ and in the Grönwall argument for uniqueness.
--
--   **Formalization Note.** The lemma's sentence lists only Assumptions 2.3, 2.4, 7.1 and 7.2; its proof invokes Proposition 7.6, which requires $0 < b \le 4a$, so that condition (a standing assumption of the paper, Assumption 2.5) is included.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 14, Lemma 7.8 ii)

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal
open Filter

namespace AdamDyn.WellPosed

/-- Lemma 7.8 ii) (p. 14). Under Assumptions 2.3, 2.4, 7.1, 7.2 (and `0 < b ≤ 4a`, used by the proof
through Prop. 7.6): for every `z0 = (x0, 0, 0) ∈ 𝒵₀` there is `c > 0` such that for every
`η ∈ [0, +∞)` and every `z ∈ Z^η_∞(z0)`, `vᵢ(t) ≥ c min(1, t)` for all `t ≥ 0` and all `i`. -/
theorem lemma_7_8_ii {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hcoer : Tendsto F (cocompact (Vec d)) atTop)
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (x0 : Vec d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (η : ℝ≥0) (z : ℝ → State d),
      IsSolutionOn a b ε F S (η : WithTop ℝ≥0) ⊤ (x0, 0, 0) z →
        ∀ t : ℝ, 0 ≤ t → ∀ i, c * min 1 t ≤ (z t).2.2 i := by sorry

end AdamDyn.WellPosed
