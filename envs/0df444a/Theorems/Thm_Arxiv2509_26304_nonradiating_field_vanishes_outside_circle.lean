-- Prove2me | Theorems.Thm_Arxiv2509_26304_nonradiating_field_vanishes_outside_circle
-- name    : Arxiv2509_26304.nonradiating_field_vanishes_outside_circle
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:07:37.997649+00:00
-- url     : https://prove2.me/theorems/0d1ae148-99e3-47e3-8013-87dbb53f49a8
-- title:
--   Section 4.3: the two-dimensional Friedlander theorem, a nonradiating field vanishes outside a circumscribing circle
-- statement:
--   Let $k>0$, let $\boldsymbol c\in\mathbb{R}^2$ and $R>0$, and let $u$ be a twice continuously differentiable solution of $(\nabla^2+k^2)u=0$ in the exterior $|\boldsymbol\rho-\boldsymbol c|>R$ of a circle that circumscribes the source. If $u$ is nonradiating, that is, its far-field amplitude (4) satisfies $F(\theta)=0$ for all $\theta$, then
--   $$u(\boldsymbol\rho)=0\qquad\text{for all }|\boldsymbol\rho-\boldsymbol c|>R.$$
--   This is the two-dimensional form of Friedlander's theorem [7, Thm. 3.2], in which the sphere is replaced by a circle.
--
--   **Formalization Note** The source enters only through the fact that the field it radiates solves the homogeneous Helmholtz equation outside the circumscribing circle, so the statement is about such fields. "Nonradiating" means that the radiated power (5) is zero. For the far-field amplitude, which is continuous here, this is the same as $F\equiv0$. The far-field amplitude is taken with respect to the origin, as in (4), and the circle may have any centre.
-- source:
--   Helsing and Karlsson, The uniqueness of inverse scattering problems, reciprocity principles, and nonradiating sources related to low-signature structures, arXiv:2509.26304v1 (2025), claim c023; Section 4.3, citing [7, Thm. 3.2], PDF p. 14

import Mathlib
import Definitions.Def_Arxiv2509_26304_Basic

open Filter Topology MeasureTheory

namespace Arxiv2509_26304

theorem nonradiating_field_vanishes_outside_circle (k : ℝ) (hk : 0 < k) (c : ℝ × ℝ) (R : ℝ)
    (hR : 0 < R) (u : ℝ × ℝ → ℂ) (hu : IsHelmholtzOn k (exteriorDisc c R) u)
    (hnr : IsNonradiating k u) :
    ∀ p ∈ exteriorDisc c R, u p = 0 := by sorry

end Arxiv2509_26304
