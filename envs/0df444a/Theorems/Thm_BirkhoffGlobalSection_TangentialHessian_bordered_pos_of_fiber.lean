-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_bordered_pos_of_fiber
-- name    : BirkhoffGlobalSection.TangentialHessian.bordered_pos_of_fiber
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:43:03.014966+00:00
-- url     : https://prove2.me/theorems/84bba05f-84e4-4d74-811e-0e22e24ab709
-- title:
--   Positive bordered Hessian on the fiber from the angle-free gate inequality
-- statement:
--   Let $K_{\mu,c}$ be the Levi-Civita regularized Hamiltonian, $g = \nabla K$ and $H = \operatorname{Hess} K$, with $r$ a free parameter. Suppose $s$ lies on the energy fiber $K_{\mu,c}(s) = 0$, and that the fiber gate data of the definitions module satisfy
--   $$G > 0 \qquad\text{and}\qquad F\,(\beta_1^2 + \beta_2^2) < G^2 .$$
--   Then the bordered form is positive:
--   $$g^{\mathsf T}\operatorname{adj}(H)\,g > 0 .$$
--
--   On the fiber circle $|u|^2 = F$, the bordered form is a degree-two trigonometric polynomial in the momentum angle. $G$ is its constant term minus the second-harmonic amplitude, and $\beta$ is its first harmonic. So the two inequalities are exactly the angle-free sufficient condition of Grisa, *Exact fiber elimination for the Levi–Civita convexity gates*, Zenodo 21270420 (2026), Theorem 3.7(b) (his gate is four times ours). The statement holds for every $\mu, c, r$.
--
--   **Formalization note.** $G, F, \beta$ are `fibG`, `fibF`, `fibBeta1`, `fibBeta2`; the fiber condition is `pP μ c s - μ * (zNormSq s / r) = 0`.
-- source:
--   Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Theorem 3.7(b).

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace BirkhoffGlobalSection.TangentialHessian

/-- (c) On the fiber `K = 0`, the bordered form of the Levi-Civita Hamiltonian is positive once the
`φ`-free inequality `fibG > 0 ∧ fibF · (β₁² + β₂²) < fibG²` holds. Valid for every `μ, c, r`. -/
theorem bordered_pos_of_fiber (μ c r : ℝ) (s : Phase)
    (hK : pP μ c s - μ * (zNormSq s / r) = 0)
    (hG : 0 < fibG μ c r s)
    (hW : fibF μ c r s * (fibBeta1 μ c r s ^ 2 + fibBeta2 μ c r s ^ 2) < fibG μ c r s ^ 2) :
    0 < kGradR μ c r s ⬝ᵥ (kHessR μ c r s).adjugate.mulVec (kGradR μ c r s) := by sorry

end BirkhoffGlobalSection.TangentialHessian
