-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_cor_7_9
-- name    : AdamDyn.WellPosed.cor_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:28.617329+00:00
-- url     : https://prove2.me/theorems/921b9d23-89c9-4f5b-92b0-c7e3b0ccde55
-- title:
--   Corollary 7.9 — global solutions of $(\mathrm{ODE}_\infty)$ and of the regularized equations $(\mathrm{ODE}_\eta)$, $\eta > 0$, exist
-- statement:
--   Let $a, \varepsilon > 0$ and $0 < b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1) and coercive (Assumption 2.3), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz (Assumption 7.2) with $S(x) > 0$ coordinatewise (Assumption 2.4). Then:
--
--   1. for every $z_0 \in \mathcal Z_+$, the autonomous equation $\dot z = h_\infty(z)$ has a global solution from $z_0$: $Z^\infty_\infty(z_0) \neq \emptyset$;
--   2. for every $z_0 \in \mathcal Z_0$ and every $\eta \in (0,+\infty)$, the regularized equation $\dot z(t) = h(t+\eta, z(t))$ has a global solution from $z_0$: $Z^\eta_\infty(z_0) \neq \emptyset$.
--
--   For $\eta > 0$ the field $h(\cdot + \eta, \cdot)$ is continuous, which is what makes the regularized equations accessible; their solutions are the approximations from which a solution of the Adam equation itself is extracted.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 15, Corollary 7.9

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal
open Filter

namespace AdamDyn.WellPosed

/-- Corollary 7.9 (p. 15). Under Assumptions 2.3, 2.4, 7.1, 7.2 and `0 < b ≤ 4a`:
`Z^∞_∞(z0) ≠ ∅` for every `z0 ∈ 𝒵₊`, and `Z^η_∞(z0) ≠ ∅` for every `(z0, η) ∈ 𝒵₀ × (0, +∞)`. -/
theorem cor_7_9 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hcoer : Tendsto F (cocompact (Vec d)) atTop)
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i) :
    (∀ z0 ∈ (Zplus : Set (State d)), ∃ z : ℝ → State d, IsSolutionOn a b ε F S ⊤ ⊤ z0 z) ∧
    (∀ z0 ∈ (Zzero : Set (State d)), ∀ η : ℝ≥0, 0 < η →
      ∃ z : ℝ → State d, IsSolutionOn a b ε F S (η : WithTop ℝ≥0) ⊤ z0 z) := by sorry

end AdamDyn.WellPosed
