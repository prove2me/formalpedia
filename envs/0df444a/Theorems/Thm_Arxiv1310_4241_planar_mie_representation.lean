-- Prove2me | Theorems.Thm_Arxiv1310_4241_planar_mie_representation
-- name    : Arxiv1310_4241.planar_mie_representation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T11:17:31.829805+00:00
-- url     : https://prove2.me/theorems/a3880f5a-43f8-45cf-ab06-627d8723a9f9
-- title:
--   Eqs. (22)-(23): the planar Lorenz-Debye-Mie representation and its normal components
-- statement:
--   Let $k=\omega\sqrt{\varepsilon\mu}$ with $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, and let $u,v$ be $C^3$ functions on the half-space $z>0$ solving $\triangle u+k^2u=0$ and $\triangle v+k^2v=0$ there. Define
--
--   $$\mathbf E=\nabla\times\nabla\times(u\hat{\mathbf z})+i\omega\mu\nabla\times(v\hat{\mathbf z}),\qquad \mathbf H=\nabla\times\nabla\times(v\hat{\mathbf z})-i\omega\varepsilon\nabla\times(u\hat{\mathbf z}).$$
--
--   Then $(\mathbf E,\mathbf H)$ is a source-free Maxwell field in $z>0$, and its normal components are
--
--   $$E_z=-\Big(\frac{\partial^2}{\partial x^2}+\frac{\partial^2}{\partial y^2}\Big)u,\qquad H_z=-\Big(\frac{\partial^2}{\partial x^2}+\frac{\partial^2}{\partial y^2}\Big)v.$$
--
--   This is the planar analogue of the Lorenz-Debye-Mie representation, with the radial direction replaced by $\hat{\mathbf z}$.
--
--   **Formalization Note** The paper does not state a regularity class; $C^3$ is the regularity at which every derivative in the statement is classical.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c003; Section IV, eqs. (22) and (23), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem planar_mie_representation (ω : ℝ) (ε μ : ℂ)
    (hk : IsCausalWavenumber (wavenumber ω ε μ)) (u v : Space → ℂ)
    (hu : ContDiffOn ℝ 3 u upperHalfSpace) (hv : ContDiffOn ℝ 3 v upperHalfSpace)
    (hHu : IsHelmholtzOn (wavenumber ω ε μ) upperHalfSpace u)
    (hHv : IsHelmholtzOn (wavenumber ω ε μ) upperHalfSpace v) :
    IsSourceFreeMaxwellOn ω ε μ upperHalfSpace (mieE ω μ u v) (mieH ω ε u v) ∧
    ∀ p ∈ upperHalfSpace, mieE ω μ u v p 2 = -transverseLaplacian u p ∧
      mieH ω ε u v p 2 = -transverseLaplacian v p := by sorry

end Arxiv1310_4241
