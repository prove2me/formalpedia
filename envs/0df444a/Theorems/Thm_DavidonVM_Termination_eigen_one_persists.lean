-- Prove2me | Theorems.Thm_DavidonVM_Termination_eigen_one_persists
-- name    : DavidonVM.Termination.eigen_one_persists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:39.557996+00:00
-- url     : https://prove2.me/theorems/45c41f40-d1a3-42a1-85de-e7819210cda0
-- title:
--   Appendix (7) — an eigenvector of HG with eigenvalue one stays one of H⁺G
-- statement:
--   Let $G$ and $H$ be symmetric real $n\times n$ matrices, $\xi\in\mathbb R^n$, $\nabla(y)=G(y-\xi)$, and $a\in\mathbb R$ arbitrary. From a point $x$ take one step
--   $$
--   x^{+}=x-H\nabla(x),\qquad \nabla^{+}=\nabla(x^{+}),\qquad H^{+}=H+a\,(H\nabla^{+})(H\nabla^{+})^{\mathsf T}.
--   $$
--   Then for every vector $u$,
--   $$
--   HGu=u\ \Longrightarrow\ H^{+}Gu=u .
--   $$
--   That is, an eigenvector of $HG$ with eigenvalue one is an eigenvector of $H^{+}G$ with eigenvalue one, display (7).
--
--   Together with (8) this is the inductive step of the hereditary property: eigenvectors with eigenvalue one accumulate along the run.
--
--   **Formalization Note** (7) holds for every coefficient $a$, so $a$ is arbitrary here. The implication is stated for all $u$, including $u=0$ where it is trivial; this is the stronger form of the paper's claim about eigenvectors. Symmetry of $G$ (a Hessian) and of $H$ (p. 4) is assumed.
-- source:
--   Davidon, Variable Metric Method for Minimization, SIAM J. Optim. 1(1) (1991), p. 17, Appendix (7)

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

open Matrix

namespace DavidonVM.Termination

/-- Appendix (7), p. 17: on the quadratic with constant symmetric Hessian `G`, if `u` satisfies
`HGu = u` for a symmetric trial matrix `H`, then after the step `x⁺ = x − H∇` and the
rank-one update `H⁺ = H + a (H∇⁺)(H∇⁺)ᵀ` with any coefficient `a`, also `H⁺Gu = u`. -/
theorem eigen_one_persists {n : ℕ} (G : Mat n) (hG : G.IsSymm) (ξ : Vec n) (H : Mat n)
    (hH : H.IsSymm) (a : ℝ) (x : Vec n) :
    let g : Vec n := grad G ξ x
    let xp : Vec n := x - H *ᵥ g
    let gp : Vec n := grad G ξ xp
    let Hp : Mat n := H + a • vecMulVec (H *ᵥ gp) (H *ᵥ gp)
    ∀ u : Vec n, H *ᵥ (G *ᵥ u) = u → Hp *ᵥ (G *ᵥ u) = u := by sorry

end DavidonVM.Termination
