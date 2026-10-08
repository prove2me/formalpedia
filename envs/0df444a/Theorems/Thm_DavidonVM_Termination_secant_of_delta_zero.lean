-- Prove2me | Theorems.Thm_DavidonVM_Termination_secant_of_delta_zero
-- name    : DavidonVM.Termination.secant_of_delta_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:12.111981+00:00
-- url     : https://prove2.me/theorems/9fb8f43e-8224-42f3-9e5b-b81f1a63f391
-- title:
--   Appendix (8) — with a = (M − N)⁻¹ the updated matrix satisfies H⁺GS = H⁺D = S
-- statement:
--   Let $G$ be a real $n\times n$ matrix, $\xi\in\mathbb R^n$, and $\nabla(y)=G(y-\xi)$ the gradient field (6). Let $H$ be a symmetric real $n\times n$ matrix and $x$ a point. Take one step of the method:
--   $$
--   \nabla=\nabla(x),\quad x^{+}=x-H\nabla,\quad \nabla^{+}=\nabla(x^{+}),\quad N=\nabla^{+\mathsf T}H\nabla^{+},\quad M=\nabla^{+\mathsf T}H\nabla ,
--   $$
--   and form the update with the coefficient of footnote 2,
--   $$
--   H^{+}=H+(M-N)^{-1}(H\nabla^{+})(H\nabla^{+})^{\mathsf T}.
--   $$
--   With $S=x^{+}-x$ and $D=\nabla^{+}-\nabla$: if $M\ne N$, then
--   $$
--   H^{+}GS=S\qquad\text{and}\qquad H^{+}D=S .
--   $$
--   So the step $S$ is an eigenvector of $H^{+}G$ with eigenvalue one, which is display (8).
--
--   This is the base case of the hereditary property: each step, once taken, is reproduced by the next trial matrix.
--
--   **Formalization Note** The paper says "when $\Delta=0$"; footnote 2 states that on a quadratic $a=(M-N)^{-1}$ gives $\Delta=0$. We read "when $\Delta=0$" through footnote 2 as "$a=(M-N)^{-1}$ with $M\ne N$" and do not formalize $\Delta$ here. No hypothesis on $G$ is needed. Symmetry of $H$ is the paper's standing assumption (p. 4). The conclusion is stated for $S$ itself (no $S\neq 0$ requirement).
-- source:
--   Davidon, Variable Metric Method for Minimization, SIAM J. Optim. 1(1) (1991), p. 17, Appendix (8) (with footnote 2, p. 16)

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

open Matrix

namespace DavidonVM.Termination

/-- Appendix (8), p. 17, with footnote 2, p. 16: one step `x⁺ = x − H∇` of the method on the
quadratic with gradient `∇ = G(x − ξ)`, followed by the update
`H⁺ = H + a (H∇⁺)(H∇⁺)ᵀ` with `a = (M − N)⁻¹`, satisfies `H⁺GS = S` and `H⁺D = S`,
where `S = x⁺ − x` and `D = ∇⁺ − ∇`. `H` is symmetric and `M ≠ N`. -/
theorem secant_of_delta_zero {n : ℕ} (G : Mat n) (ξ : Vec n) (H : Mat n) (hH : H.IsSymm)
    (x : Vec n) :
    let g : Vec n := grad G ξ x
    let xp : Vec n := x - H *ᵥ g
    let gp : Vec n := grad G ξ xp
    let Nv : ℝ := gp ⬝ᵥ (H *ᵥ gp)
    let Mv : ℝ := gp ⬝ᵥ (H *ᵥ g)
    let Hp : Mat n := H + (Mv - Nv)⁻¹ • vecMulVec (H *ᵥ gp) (H *ᵥ gp)
    let S : Vec n := xp - x
    let D : Vec n := gp - g
    Mv ≠ Nv → Hp *ᵥ (G *ᵥ S) = S ∧ Hp *ᵥ D = S := by sorry

end DavidonVM.Termination
