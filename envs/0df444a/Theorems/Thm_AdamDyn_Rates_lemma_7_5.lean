-- Prove2me | Theorems.Thm_AdamDyn_Rates_lemma_7_5
-- name    : AdamDyn.Rates.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:49.516435+00:00
-- url     : https://prove2.me/theorems/e084a218-bbd4-4401-b642-df8bfd1884bd
-- title:
--   Lemma 7.5 (V part) — $V$ decreases along the non-autonomous Adam field when $0<b\le 4a$
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1) and let $S:\mathbb R^d\to[0,+\infty)^d$ be locally Lipschitz (Assumption 7.2). Let $\varepsilon>0$ and $0<b\le 4a$. Let $h$ be the Adam vector field (3.3) and $U,V$ the functions (3.4)–(3.5).
--
--   Consider $t>0$ and $z=(x,m,v)$ with $v_i>0$ for every $i$. Then $V$ is differentiable at $(t,z)$ and
--
--   $$\big\langle \nabla V(t,z),\,(1,h(t,z))\big\rangle\ \le\ -\frac{\varepsilon}{2}\left\|\frac{a\,m}{U(t,v)}\right\|^2 ,$$
--
--   where $am/U(t,v)$ is the vector with coordinates $a m_i/U_i(t,v)$.
--
--   This is the inequality that makes $t\mapsto V(t,z(t))$ non-increasing along solutions of the Adam ODE; in the convergence-rate proof it bounds the derivative of the first term of $\tilde W_\delta$. The condition $b\le 4a$ is where the relation between the two Adam averaging parameters enters.
--
--   **Formalization Note** $V$ is regarded as a function of the pair $(t,z)\in\mathbb R\times\mathcal Z$; $\langle\nabla V(t,z),(1,h(t,z))\rangle$ is its Fréchet derivative at $(t,z)$ applied to the vector $(1,h(t,z))$. The paper's Lemma 7.5 also contains the analogous inequality for $V_\infty$ and $h_\infty$, which is not stated here.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, pp. 12–13, Lemma 7.5 (second inequality)

import Mathlib
import Definitions.Def_AdamDyn_Rates_AdamField
import Definitions.Def_AdamDyn_Rates_Lyapunov

namespace AdamDyn.Rates

/-- Lemma 7.5, the `V` part (Barakat–Bianchi, pp. 12–13). Under Assumptions 7.1 and 7.2 and
`0 < b ≤ 4a`, for `t > 0` and `z = (x, m, v) ∈ 𝒵₊*` (all `vᵢ > 0`), `V` is differentiable at
`(t, z)` and `⟨∇V(t, z), (1, h(t, z))⟩ ≤ −(ε/2) ‖a m / U(t, v)‖²`. -/
theorem lemma_7_5 {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε t : ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hS0 : ∀ x i, 0 ≤ S x i)
    (hε : 0 < ε) (hb : 0 < b) (hba : b ≤ 4 * a)
    (ht : 0 < t) (hv : ∀ i, 0 < z.2.2 i) :
    DifferentiableAt ℝ
        (fun p : ℝ × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d)) => V F a b ε p.1 p.2) (t, z) ∧
      fderiv ℝ
          (fun p : ℝ × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d)) => V F a b ε p.1 p.2) (t, z)
          (1, adamField F S a b ε t z) ≤
        -(ε / 2) * ∑ i, (a * z.2.1 i / U a b ε t z.2.2 i) ^ 2 := by sorry

end AdamDyn.Rates
