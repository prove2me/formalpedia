-- Prove2me | Theorems.Thm_Arxiv1310_4241_maxwell_field_determined_by_normal_components
-- name    : Arxiv1310_4241.maxwell_field_determined_by_normal_components
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:08:39.621594+00:00
-- url     : https://prove2.me/theorems/7f2a1e92-2b07-4295-99f0-f2e77a0b5baa
-- title:
--   Eq. (21): a radiating Maxwell field in $z>0$ is determined by $E_z$ and $H_z$
-- statement:
--   Let $\omega\in\mathbb R$ and $\varepsilon,\mu\in\mathbb C$ with $k=\omega\sqrt{\varepsilon\mu}$ satisfying $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$. Let $(\mathbf E_1,\mathbf H_1)$ and $(\mathbf E_2,\mathbf H_2)$ be time-harmonic Maxwell fields in the source-free half-space $z>0$:
--
--   $$\nabla\times\mathbf E_m=i\omega\mu\mathbf H_m,\qquad \nabla\times\mathbf H_m=-i\omega\varepsilon\mathbf E_m,\qquad \nabla\cdot\mathbf E_m=\nabla\cdot\mathbf H_m=0,$$
--
--   both satisfying the radiation condition (3), $\mathbf H_m(\mathbf x)\times\hat{\mathbf r}-\frac{\mu}{\varepsilon}\mathbf E_m(\mathbf x)\to0$ as $|\mathbf x|\to\infty$ in $z>0$. If $E_{1,z}=E_{2,z}$ and $H_{1,z}=H_{2,z}$ in $z>0$, then $\mathbf E_1=\mathbf E_2$ and $\mathbf H_1=\mathbf H_2$ in $z>0$.
--
--   That is, a radiating Maxwell field in the half-space is determined by its normal components, which is what justifies representing it through two scalar potentials.
--
--   **Formalization Note** The fields are assumed differentiable in $z>0$, the region of the representation (22), and the radiation condition is eq. (3) exactly as printed, with the limit taken over points of $z>0$. The paper's argument lists only the fields $e^{ikz}$; the statement is the uniqueness claim itself.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c002; Section IV, paragraph containing eq. (21), PDF p. 7; radiation condition eq. (3), Section I, PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem maxwell_field_determined_by_normal_components (ω : ℝ) (ε μ : ℂ)
    (hk : IsCausalWavenumber (wavenumber ω ε μ)) (E₁ H₁ E₂ H₂ : Space → Fin 3 → ℂ)
    (h₁ : IsSourceFreeMaxwellOn ω ε μ upperHalfSpace E₁ H₁)
    (h₂ : IsSourceFreeMaxwellOn ω ε μ upperHalfSpace E₂ H₂)
    (hr₁ : SilverMullerAsPrinted ε μ upperHalfSpace E₁ H₁)
    (hr₂ : SilverMullerAsPrinted ε μ upperHalfSpace E₂ H₂)
    (hEz : ∀ p ∈ upperHalfSpace, E₁ p 2 = E₂ p 2) (hHz : ∀ p ∈ upperHalfSpace, H₁ p 2 = H₂ p 2) :
    ∀ p ∈ upperHalfSpace, E₁ p = E₂ p ∧ H₁ p = H₂ p := by sorry

end Arxiv1310_4241
