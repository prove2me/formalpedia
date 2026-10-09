-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_eq_3_10
-- name    : ExtraConsensus.Sublinear.eq_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:37.951868+00:00
-- url     : https://prove2.me/theorems/1613a8bc-8074-4d3b-ac6a-34d285eb6e6e
-- title:
--   Eq. (3.10), first line, p. 11 — co-coercivity of ∇f: (2α/L_f)‖∇f(a) − ∇f(b)‖²_F ≤ 2α⟨a − b, ∇f(a) − ∇f(b)⟩
-- statement:
--   Under Assumption 2 (each $f_i$ convex and differentiable with $L_{\mathbf f}$-Lipschitz gradient, $L_{\mathbf f}\ge0$) and for $\alpha>0$, every pair of stacked points $\mathbf a,\mathbf b\in\mathbb R^{n\times p}$ satisfies
--   $$2\alpha\,\|\nabla\mathbf f(\mathbf a)-\nabla\mathbf f(\mathbf b)\|_F^2\ \le\ 2\alpha L_{\mathbf f}\,\langle\mathbf a-\mathbf b,\nabla\mathbf f(\mathbf a)-\nabla\mathbf f(\mathbf b)\rangle .$$
--   For $L_{\mathbf f}>0$ this is the paper's $\frac{2\alpha}{L_{\mathbf f}}\|\nabla\mathbf f(\mathbf x^k)-\nabla\mathbf f(\mathbf x^*)\|_F^2\le2\alpha\langle\mathbf x^k-\mathbf x^*,\nabla\mathbf f(\mathbf x^k)-\nabla\mathbf f(\mathbf x^*)\rangle$ multiplied by $L_{\mathbf f}$.
--
--   It is the inequality that opens the proof of Theorem 3.3.
--
--   **Formalization Note** The inequality is multiplied through by $L_{\mathbf f}$ so that no division by $L_{\mathbf f}$ occurs (at $L_{\mathbf f}=0$ it says the gradient differences vanish). The page states it at the pair $(\mathbf x^k,\mathbf x^*)$; the statement here is for every pair, which is what the page's justification ("$\nabla\mathbf f$ is Lipschitz continuous") gives.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §3.2, proof of Theorem 3.3, eq. (3.10) first line, p. 11

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Eq. (3.10), first line, p. 11, multiplied by `L_𝐟` and stated for every pair of stacked
points: under Assumption 2 and `α > 0`,
`2α‖∇𝐟(𝐚) − ∇𝐟(𝐛)‖²_F ≤ 2α L_𝐟 ⟨𝐚 − 𝐛, ∇𝐟(𝐚) − ∇𝐟(𝐛)⟩`. -/
theorem eq_3_10 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α : ℝ)
    (hA2 : ConvexLipschitzGrad f Lf) (hα0 : 0 < α) :
    ∀ a b : Stack n p,
      2 * α * frob (gradF f a - gradF f b) (gradF f a - gradF f b) ≤
        2 * α * Lf * frob (a - b) (gradF f a - gradF f b) := by sorry

end ExtraConsensus.Sublinear
