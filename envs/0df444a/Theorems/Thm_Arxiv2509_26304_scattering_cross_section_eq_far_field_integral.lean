-- Prove2me | Theorems.Thm_Arxiv2509_26304_scattering_cross_section_eq_far_field_integral
-- name    : Arxiv2509_26304.scattering_cross_section_eq_far_field_integral
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:06:42.116082+00:00
-- url     : https://prove2.me/theorems/e382f221-a3ce-4925-aba5-cec5ca52627c
-- title:
--   Eq. (9): the scattering cross section of a plane wave is the integral of $|F^{\rm sc}|^2$
-- statement:
--   Let $\eta_0>0$, $k>0$, $\alpha\in\mathbb{R}$ and $R>0$. Let $u$ be a twice continuously differentiable solution of $(\nabla^2+k^2)u=0$ in $|\boldsymbol\rho|>R$ with far-field amplitude $F$ in the sense of (4). Then for every $r>R$ the total scattering cross section (6) for the plane wave (7) with angle of incidence $\alpha$ is
--   $$\Sigma=\frac{\text{time average of scattered power per unit length through }\rho=r}{\text{time average of incident power density}}=\int_{-\pi}^{\pi}|F(\theta)|^2\,d\theta,$$
--   which is eq. (9), $\Sigma=\eta_0^{-1}P$, with $P$ given by eq. (5).
--
--   **Formalization Note** The scattered field $u$ is any outgoing field outside a disc containing the structure; the identity does not use the boundary conditions. Both time averages are taken with the paper's convention $\operatorname{Re}\{\cdot\,e^{-i\omega t}\}$, so they carry the factor $\tfrac12$: the incident density is $\eta_0/2$ and the scattered power is $\frac{\eta_0}{2}\int|F|^2$. The statement is therefore eq. (9) with (5) substituted, $\Sigma=\int|F|^2$; it does not assert that (5) is the time-averaged power, which is $\frac{\eta_0}{2}\int|F|^2$, half of (5). The scattered power is measured through a circle $|\boldsymbol\rho|=r$ outside the structure, and the statement holds for every such $r$.
-- source:
--   Helsing and Karlsson, The uniqueness of inverse scattering problems, reciprocity principles, and nonradiating sources related to low-signature structures, arXiv:2509.26304v1 (2025), claim c022; Section 2, eqs. (5), (6), (7), (9), PDF p. 5 (time convention PDF p. 3)

import Mathlib
import Definitions.Def_Arxiv2509_26304_Basic

open Filter Topology MeasureTheory

namespace Arxiv2509_26304

theorem scattering_cross_section_eq_far_field_integral (eta0 k α : ℝ) (heta0 : 0 < eta0)
    (hk : 0 < k) (R : ℝ) (hR : 0 < R) (u : ℝ × ℝ → ℂ)
    (hu : IsHelmholtzOn k (exteriorDisc (0, 0) R) u) (F : ℝ → ℂ)
    (hF : HasFarFieldAmplitude k u F) :
    ∀ r : ℝ, R < r →
      scatteringCrossSection eta0 k α u r = ∫ θ in (-Real.pi)..Real.pi, ‖F θ‖ ^ 2 := by sorry

end Arxiv2509_26304
