-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_angle_linear_growth
-- name    : BirkhoffGlobalSection.saddle_center_angle_linear_growth
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T19:04:10.689188+00:00
-- url     : https://prove2.me/theorems/3e8ab39d-e283-479c-8570-ae94e3064f0f
-- title:
--   Linear ambient-angle growth from the spectral splitting
-- statement:
--   From the spectral splitting, the ambient determinant angle grows at a uniform linear rate. The elliptic plane forces steady rotation while the hyperbolic directions contribute only a bounded wobble, so for fixed rate $c_0>0$ and constant $C_0$, on every interval $[a,a+L]$ the fundamental solution admits a continuous ambient angle with
--
--   $$
--   \alpha_0(a+L)-\alpha_0(a) > c_0 L - C_0.
--   $$
--
--   This is the quantitative core of the rotation mechanism: it turns the algebraic splitting into the uniform estimate from which unboundedness follows by pure logic. The constants depend only on the splitting data.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S7, Eq. (7.7) and the proof of Theorem 1.8 (the linearized flow at the saddle-center splits into a hyperbolic and an elliptic part, and the elliptic part forces index growth). Gutt, https://arxiv.org/pdf/1307.7239, Eq. (9). H0 is the Hessian of the platform Levi-Civita Hamiltonian at mu = 1/2, c = 2.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

namespace BirkhoffGlobalSection

theorem saddle_center_angle_linear_growth
    (ω lam : ℝ) (hω : 0 < ω) (hlam : 0 < lam)
    (e₁ e₂ f₁ f₂ : Phase)
    (he₁ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₁)) = ω • e₂)
    (he₂ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec e₂)) = -ω • e₁)
    (hf₁ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₁)) = lam • f₁)
    (hf₂ : TangentialHessian.qI.mulVec
        (((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) ℝ).mulVec f₂)) = -lam • f₂)
    (hindep : LinearIndependent ℝ ![e₁, e₂, f₁, f₂]) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C₀ : ℝ, ∀ a L : ℝ,
      ∃ (Φ0 : ℝ → (Phase →L[ℝ] Phase)) (α0 : ℝ → ℝ),
        Φ0 a = ContinuousLinearMap.id ℝ Phase ∧
        (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
          HasDerivAt (fun τ => Φ0 τ v)
            (TangentialHessian.qI.mulVec
              ((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
                Matrix (Fin 4) (Fin 4) ℝ).mulVec (Φ0 t v))) t) ∧
        ContinuousOn α0 (Set.Icc a (a + L)) ∧
        (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
          ambientRotationDet (Φ0 t) = ⟨ρ * Real.cos (α0 t), ρ * Real.sin (α0 t)⟩) ∧
        c₀ * L - C₀ < α0 (a + L) - α0 a := by sorry

end BirkhoffGlobalSection
