-- Prove2me | Theorems.Thm_FamousTheorems_second_derivative_symmetric
-- name    : FamousTheorems.second_derivative_symmetric
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:39:58.372865+00:00
-- url     : https://prove2.me/theorems/75f1af52-dd64-44bf-b502-8b9567e3cd22
-- title:
--   Symmetry of second derivatives (Clairaut–Schwarz)
-- statement:
--   **Symmetry of second derivatives.** For a twice-differentiable function, the second derivative is a symmetric bilinear map: $$D^2f(x)(u,v) = D^2f(x)(v,u).$$ Partial derivatives commute — $\partial_i\partial_j f = \partial_j\partial_i f$ — which is why a Hessian is a symmetric matrix and why mixed partials can be taken in any order. The result needs a genuine hypothesis: it fails for functions whose second partials exist but are not continuous, the standard counterexample being $xy(x^2-y^2)/(x^2+y^2)$ at the origin. Symmetry of the Hessian is what makes the second-derivative test a statement about real eigenvalues, and in differential geometry it is the reason the Levi-Civita connection is torsion-free. **Formalization note.** The statement is for the Fréchet second derivative on a normed space, so it covers infinite-dimensional domains. The result is Mathlib's `second_derivative_symmetric`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem second_derivative_symmetric :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} {F : Type u_3} 
    [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] 
    {f : E → F} [IsRCLikeNormedField 𝕜] {f' : E → E →L[𝕜] F} {f'' : E →L[𝕜] E →L[𝕜] F} {x : E}, 
    (∀ (y : E), HasFDerivAt f (f' y) y) → HasFDerivAt f' f'' x → ∀ (v w : E), (f'' v) w = (f'' w) v := by sorry

end FamousTheorems
