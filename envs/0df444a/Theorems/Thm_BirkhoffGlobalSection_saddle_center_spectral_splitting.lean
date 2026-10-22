-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_spectral_splitting
-- name    : BirkhoffGlobalSection.saddle_center_spectral_splitting
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T19:04:08.062373+00:00
-- url     : https://prove2.me/theorems/bd26a4c7-fc4e-4ed5-a3e3-3491d4ba6b62
-- title:
--   Spectral splitting of the saddle-center linearization
-- statement:
--   At $\mu=1/2$, $c=2$ the saddle-center linearization $JH_0$ splits: there are an elliptic speed $\omega>0$, a hyperbolic rate $\lambda>0$, and four independent directions with
--
--   $$
--   JH_0 e_1 = \omega e_2, \qquad JH_0 e_2 = -\omega e_1, \qquad JH_0 f_1 = \lambda f_1, \qquad JH_0 f_2 = -\lambda f_2.
--   $$
--
--   This is pure linear algebra of the explicit Hessian $H_0$ at $(\pm\tfrac12,0,0,0)$: the characteristic polynomial $\lambda^4-6\lambda^2-119$ has one imaginary and one real pair. It packages the rotation fact driving all subsequent index growth, with no analysis.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S7, Eq. (7.7) and the proof of Theorem 1.8 (the linearized flow at the saddle-center splits into a hyperbolic and an elliptic part, and the elliptic part forces index growth). Gutt, https://arxiv.org/pdf/1307.7239, Eq. (9). H0 is the Hessian of the platform Levi-Civita Hamiltonian at mu = 1/2, c = 2.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

namespace BirkhoffGlobalSection

theorem saddle_center_spectral_splitting :
    ∃ ω lam : ℝ, 0 < ω ∧ 0 < lam ∧ ∃ e₁ e₂ f₁ f₂ : Phase,
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₁)) = ω • e₂ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₂)) = -ω • e₁ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₁)) = lam • f₁ ∧
      TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₂)) = -lam • f₂ ∧
      LinearIndependent ℝ ![e₁, e₂, f₁, f₂] := by sorry

end BirkhoffGlobalSection
