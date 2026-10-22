-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_linear_system_rotation_growth
-- name    : BirkhoffGlobalSection.saddle_center_linear_system_rotation_growth
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T03:39:36.620882+00:00
-- url     : https://prove2.me/theorems/69c9fd3d-c777-42b1-9e33-e3a7cb0a2bf3
-- title:
--   Robust rotation growth for the saddle-center linear model
-- statement:
--   Let $J=\begin{pmatrix}0&I_2\\-I_2&0\end{pmatrix}$ and fix the symmetric matrix
--
--   $$H_0=\begin{pmatrix}-16&0&0&1\\0&8&-1&0\\0&-1&1&0\\1&0&0&1\end{pmatrix}.$$
--
--   For every $R\in\mathbb R$, there exist $\delta,L>0$ with the following property. Let $a\in\mathbb R$ and let $H(t)$ be a continuous real symmetric matrix on $[a,a+L]$, satisfying $\|H(t)-H_0\|_{\max}<\delta$ throughout this interval. Suppose a family of real linear maps $Y(t):\mathbb R^4\to\mathbb R^4$ satisfies the variational equation $\frac{d}{dt}(Y(t)v)=JH(t)Y(t)v$ for every vector $v$ and every $t\in[a,a+L]$, and $Y(a)$ is symplectic: $(Y(a)u)^T JY(a)v=u^TJv$ for all $u,v$.
--
--   Write $P(Y(t))$ for the complex-linear part in coordinates $z=q-ip$. Every continuous angle $\alpha:\mathbb R\to\mathbb R$ with $\det_{\mathbb C}P(Y(t))=\rho(t)e^{i\alpha(t)}$ for some $\rho(t)>0$ at each time satisfies
--
--   $$\alpha(a+L)-\alpha(a)>R.$$
--
--   The constants are uniform in the initial time and in the initial symplectic matrix. This finite-dimensional perturbation estimate isolates the local rotation mechanism needed near the Levi–Civita saddle-center equilibria.
--
--   **Formalization Note** The matrix norm is the entrywise maximum norm. The coefficients and differential equation are constrained only on the specified interval; the angle is supplied globally.
-- source:
--   Derived finite-time robustness formulation of the saddle-center growth mechanism in Liu–Salomão, https://arxiv.org/html/2506.17867v2#S7, Eq. (7.7) and the final proof of Theorem 1.8. The determinant rotation map is Gutt, https://arxiv.org/pdf/1307.7239, Corollary 12, Eq. (9), pp. 8–9. H0 is the directly computed Hessian of the platform Levi–Civita Hamiltonian at μ=1/2, c=2, s=(±1/2,0,0,0). The coefficient perturbation estimate and arbitrary symplectic initial-matrix formulation are derived auxiliary claims, not a verbatim theorem from either reference.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.Analysis.Matrix.Normed
open scoped Matrix.Norms.Elementwise

namespace BirkhoffGlobalSection

/-- Finite-time stability of positive ambient rotation for the explicit
saddle-center linear model. The initial symplectic map is unrestricted in
size, and all coefficient assumptions are confined to the resident interval. -/
theorem saddle_center_linear_system_rotation_growth (R : ℝ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧
      ∀ (a : ℝ) (H : ℝ → Matrix (Fin 4) (Fin 4) ℝ),
        ContinuousOn H (Set.Icc a (a + L)) →
        (∀ t ∈ Set.Icc a (a + L), ∀ i j : Fin 4, H t i j = H t j i) →
        (∀ t ∈ Set.Icc a (a + L),
          ‖H t - !![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1]‖ < δ) →
        ∀ Y : ℝ → (Phase →L[ℝ] Phase),
          (∀ u v : Phase,
            Y a u ⬝ᵥ TangentialHessian.qI.mulVec (Y a v) =
              u ⬝ᵥ TangentialHessian.qI.mulVec v) →
          (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
            HasDerivAt (fun τ => Y τ v)
              (TangentialHessian.qI.mulVec ((H t).mulVec (Y t v))) t) →
          ∀ α : ℝ → ℝ, IsAmbientRotationAngle Y α →
            R < α (a + L) - α a := by sorry

end BirkhoffGlobalSection
