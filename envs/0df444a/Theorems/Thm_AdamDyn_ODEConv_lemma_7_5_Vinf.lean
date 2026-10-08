-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_lemma_7_5_Vinf
-- name    : AdamDyn.ODEConv.lemma_7_5_Vinf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:45.307705+00:00
-- url     : https://prove2.me/theorems/6982c0a3-1b95-49ae-99f7-64d82914e257
-- title:
--   Lemma 7.5 ($V_\infty$ part) — $V_\infty$ decreases along $h_\infty$ when $0 < b \le 4a$
-- statement:
--   Let $F$ be continuously differentiable with locally Lipschitz gradient, and $S : \mathbb R^d \to [0,+\infty)^d$ locally Lipschitz (Assumptions 7.1, 7.2). Assume $0 < b \le 4a$ and $\varepsilon > 0$. Let $z = (x, m, v) \in \mathcal Z_+^*$. Then $V_\infty$ is differentiable at $z$ and
--   $$\langle \nabla V_\infty(z), h_\infty(z) \rangle \le -\varepsilon \Big\| \frac{a m}{U_\infty(v)} \Big\|^2 = -\varepsilon \sum_{i=1}^d \Big(\frac{a m_i}{a(\varepsilon + \sqrt{v_i})}\Big)^2 .$$
--
--   This is the first inequality of Lemma 7.5; the second one, for the non-autonomous $V$, is not stated here. It is the first term of the derivative of $W_\delta$ in Proposition 7.15.
--
--   **Formalization Note** $\langle \nabla V_\infty(z), h_\infty(z)\rangle$ is written as the Fréchet derivative of $V_\infty$ at $z$ applied to $h_\infty(z)$, which is the same number.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, pp. 12–13, Lemma 7.5 (first inequality)

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField
import Definitions.Def_AdamDyn_ODEConv_LyapunovW

namespace AdamDyn.ODEConv

/-- Lemma 7.5, the `V∞` part (Barakat & Bianchi, arXiv:1810.02263v4, pp. 12–13). Let
Assumptions 7.1 and 7.2 hold and `0 < b ≤ 4a`. For `z = (x, m, v) ∈ 𝒵₊*`, `V∞` is differentiable
at `z` and `⟨∇V∞(z), h∞(z)⟩ ≤ −ε ‖am/U∞(v)‖²`. The pairing `⟨∇V∞(z), h∞(z)⟩` is the Fréchet
derivative of `V∞` at `z` applied to `h∞(z)`, and `‖am/U∞(v)‖² = ∑ᵢ (a mᵢ / U∞(v)ᵢ)²`. -/
theorem lemma_7_5_Vinf {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSnn : ∀ x i, 0 ≤ S x i)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (z : AdamDyn.WellPosed.State d) (hz : InZplusStar z) :
    DifferentiableAt ℝ (Vinf a ε F) z ∧
      fderiv ℝ (Vinf a ε F) z (adamFieldInf a b ε F S z) ≤
        -ε * ∑ i, (a * z.2.1 i / Uinf a ε z.2.2 i) ^ 2 := by sorry

end AdamDyn.ODEConv
