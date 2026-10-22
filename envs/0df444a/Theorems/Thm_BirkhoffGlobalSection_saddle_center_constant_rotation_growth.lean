-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_constant_rotation_growth
-- name    : BirkhoffGlobalSection.saddle_center_constant_rotation_growth
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T17:49:43.641236+00:00
-- url     : https://prove2.me/theorems/e5ece3e8-dbbf-4f4e-a243-80d52e0f9b99
-- title:
--   Unbounded rotation of the saddle-center linearization
-- statement:
--   Unbounded ambient rotation of the linearized flow at the equal-mass saddle-center.
--
--   Let $J$ be the Hamiltonian complex structure and let
--
--   $$
--   H_0=\begin{pmatrix}-16&0&0&1\\0&8&-1&0\\0&-1&1&0\\1&0&0&1\end{pmatrix}
--   $$
--
--   be the Hessian of the Levi-Civita Hamiltonian at the saddle-center $(\pm\tfrac12,0,0,0)$ for $\mu=\tfrac12$, $c=2$. For every $R\in\mathbb R$ there is $L>0$ with the following property. For every $a\in\mathbb R$, there are a fundamental solution $\Phi_0$ of
--
--   $$
--   \Phi_0'=JH_0\,\Phi_0,\qquad \Phi_0(a)=\mathrm{id},
--   $$
--
--   on $[a,a+L]$, and a continuous function $\alpha_0$ on $[a,a+L]$ with $d(\Phi_0(t))=\rho(t)e^{i\alpha_0(t)}$ and $\rho(t)>0$, such that
--
--   $$
--   \alpha_0(a+L)-\alpha_0(a)>R .
--   $$
--
--   Here $d$ is the ambient determinant, the determinant of the complex-linear part in the coordinates $z=q-ip$. The matrix $JH_0$ has one hyperbolic and one elliptic pair of eigenvalues. This statement is the linear rotation mechanism behind the high-index estimate near the saddle-center.
--
--   **Formalization Note** The fundamental solution and the angle are asserted to exist on each interval of length $L$. The equation is `HasDerivAt (fun τ => Φ₀ τ v) (qI.mulVec (H₀.mulVec (Φ₀ t v))) t` on the interval.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S7, Eq. (7.7) and the proof of Theorem 1.8 (the linearized flow at the saddle-center splits into a hyperbolic and an elliptic part, and the elliptic part forces index growth). Gutt, Generalized Conley--Zehnder index, https://arxiv.org/pdf/1307.7239, Eq. (9). H0 is the Hessian of the platform Levi-Civita Hamiltonian at mu = 1/2, c = 2, s = (+-1/2, 0, 0, 0).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

namespace BirkhoffGlobalSection

/-- The linearization at the equal-mass Levi-Civita saddle-center rotates
without bound. For every `R` there is a length `L` such that, on every interval
`[a, a + L]`, the fundamental solution of `Φ' = J H₀ Φ` with `Φ(a) = id` admits
a continuous ambient angle whose increment exceeds `R`. -/
theorem saddle_center_constant_rotation_growth (R : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ,
      ∃ (Φ₀ : ℝ → (Phase →L[ℝ] Phase)) (α₀ : ℝ → ℝ),
        Φ₀ a = ContinuousLinearMap.id ℝ Phase ∧
        (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
          HasDerivAt (fun τ => Φ₀ τ v)
            (TangentialHessian.qI.mulVec
              ((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
                Matrix (Fin 4) (Fin 4) ℝ).mulVec (Φ₀ t v))) t) ∧
        ContinuousOn α₀ (Set.Icc a (a + L)) ∧
        (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
          ambientRotationDet (Φ₀ t) = ⟨ρ * Real.cos (α₀ t), ρ * Real.sin (α₀ t)⟩) ∧
        R < α₀ (a + L) - α₀ a := by sorry

end BirkhoffGlobalSection
