-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_lemma_7_5
-- name    : AdamDyn.WellPosed.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:45.837966+00:00
-- url     : https://prove2.me/theorems/4a3b5c14-c57b-4b3c-a642-9639c804103a
-- title:
--   Lemma 7.5 — $V$ and $V_\infty$ decrease along the Adam fields when $0 < b \le 4a$
-- statement:
--   Let $\varepsilon > 0$ and $0 < b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1), and let $S : \mathbb R^d \to [0,+\infty)^d$ be locally Lipschitz (Assumption 7.2). Let $t > 0$ and $z = (x, m, v) \in \mathcal Z_+^*$ (so $v_i > 0$ for all $i$). Then the Lyapunov function $V$ of (3.4) is differentiable at $(t, z)$ as a function of $(t,z) \in \mathbb R \times \mathcal Z$, the function $V_\infty$ is differentiable at $z$, and
--   $$\langle \nabla V_\infty(z), h_\infty(z) \rangle \le -\varepsilon \sum_{i=1}^d \left(\frac{a\, m_i}{U_\infty(v_i)}\right)^2,$$
--   $$\langle \nabla V(t, z), (1, h(t,z)) \rangle \le -\frac{\varepsilon}{2} \sum_{i=1}^d \left(\frac{a\, m_i}{U(t, v_i)}\right)^2 .$$
--   Here $\langle \nabla V(t,z), (1, h(t,z))\rangle$ is the derivative of $V$ at $(t,z)$ in the direction $(1, h(t,z))$, i.e. the rate of change of $V(t, z(t))$ along a solution of $\dot z = h(t,z)$ passing through $z$ at time $t$.
--
--   This is the Lyapunov inequality behind both the existence proof (through the uniform bound of Proposition 7.6) and the convergence analysis of the Adam dynamics; the condition $b \le 4a$ is exactly what makes the time derivative of the bias-correction factors harmless.
--
--   **Formalization Note.** The two inner products are written as the Fréchet derivatives `fderiv` of $(t,z) \mapsto V(t,z)$ and of $V_\infty$ applied to $(1, h(t,z))$ and to $h_\infty(z)$; differentiability is asserted, so these are the true derivatives. The squared norm $\|am/U\|^2$ is written as the explicit coordinate sum.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, pp. 12–13, Lemma 7.5

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField
import Definitions.Def_AdamDyn_WellPosed_lyapunov

open scoped NNReal

namespace AdamDyn.WellPosed

/-- Lemma 7.5 (pp. 12–13). Under Assumptions 7.1–7.2 and `0 < b ≤ 4a`, for `t > 0` and
`z = (x, m, v) ∈ 𝒵₊*`: `V` is differentiable at `(t, z)`, `V∞` is differentiable at `z`,
`⟨∇V∞(z), h∞(z)⟩ ≤ −ε ‖am/U∞(v)‖²` and `⟨∇V(t, z), (1, h(t, z))⟩ ≤ −(ε/2) ‖am/U(t, v)‖²`. -/
theorem lemma_7_5 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSnn : ∀ x i, 0 ≤ S x i)
    (t : ℝ) (ht : 0 < t) (z : State d) (hz : z ∈ ZplusStar) :
    DifferentiableAt ℝ (fun p : ℝ × State d => lyapV a b ε F p.1 p.2) (t, z) ∧
      DifferentiableAt ℝ (lyapVInf a ε F) z ∧
      fderiv ℝ (lyapVInf a ε F) z (adamFieldInf a b ε F S z) ≤
        -ε * ∑ i, (a * z.2.1 i / lyapUInf a ε (z.2.2 i)) ^ 2 ∧
      fderiv ℝ (fun p : ℝ × State d => lyapV a b ε F p.1 p.2) (t, z) (1, adamField a b ε F S t z) ≤
        -(ε / 2) * ∑ i, (a * z.2.1 i / lyapU a b ε t (z.2.2 i)) ^ 2 := by sorry

end AdamDyn.WellPosed
