-- Prove2me | Theorems.Thm_Arxiv2210_02565_hemispherical_bump_image_solution
-- name    : Arxiv2210_02565.hemispherical_bump_image_solution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T13:01:48.164274+00:00
-- url     : https://prove2.me/theorems/0f8ca93a-c070-441d-9cdb-fb2c04596d8d
-- title:
--   Appendix A: image/Mie solution of the PEC hemispherical bump
-- statement:
--   Let $k>0$, $a>0$, $E_0\in\mathbb C$, $0\le\alpha\le\pi/2$, and fix a polarization (TE or TM). Consider the PEC half-space $\{z<0\}$ with a PEC hemispherical bump of radius $a$ centred at the origin, whose boundary is $\Gamma=\{z=0,\ |\mathbf r|\ge a\}\cup\{|\mathbf r|=a,\ z\ge0\}$. Let $\mathbf E^{\rm inc}_\alpha(\mathbf r)=E_0e^{ik(y\cos\alpha-z\sin\alpha)}\mathbf q$ with $\mathbf q=\hat{\mathbf x}$ (TE) or $\hat{\mathbf y}\sin\alpha+\hat{\mathbf z}\cos\alpha$ (TM). Let $\widetilde{\mathbf E}^{\rm inc}=-\mathbf E^{\rm inc}_{-\alpha}$ (TE) or $\mathbf E^{\rm inc}_{-\alpha}$ (TM), and let $\mathbf E^{\rm Mie}$, $\widetilde{\mathbf E}^{\rm Mie}$ be the fields scattered by the entire PEC sphere $|\mathbf r|\le a$ under $\mathbf E^{\rm inc}_\alpha$ and $\widetilde{\mathbf E}^{\rm inc}$. Then the field
--
--   $$\mathbf E^{\rm tot}=\mathbf E^{\rm inc}_\alpha+\mathbf E^{\rm Mie}+\widetilde{\mathbf E}^{\rm inc}+\widetilde{\mathbf E}^{\rm Mie}$$
--
--   satisfies the PEC condition $\hat{\mathbf n}\times\mathbf E^{\rm tot}=\mathbf 0$ on $\Gamma$:
--
--   1. $\hat{\mathbf z}\times\mathbf E^{\rm tot}(\mathbf r)=\mathbf 0$ for $z=0$, $|\mathbf r|\ge a$;
--   2. $\mathbf r\times\mathbf E^{\rm tot}(\mathbf r)=\mathbf 0$ for $|\mathbf r|=a$, $z\ge0$.
--
--   It also solves Maxwell's equations above $\Gamma$:
--
--   3. $\nabla\times\nabla\times\mathbf E^{\rm tot}=k^2\mathbf E^{\rm tot}$ for $z>0$, $|\mathbf r|>a$.
--
--   Its scattered part relative to the flat-PEC source field, $\mathbf E^{\rm s}=\mathbf E^{\rm tot}-\mathbf E^{\rm inc}_\alpha-\widetilde{\mathbf E}^{\rm inc}$, satisfies the Silver-Müller radiation condition (3) in $\{z>0\}$:
--
--   4. $|\mathbf r|\big((\nabla\times\mathbf E^{\rm s})\times\hat{\mathbf r}-ik\mathbf E^{\rm s}\big)\to\mathbf 0$ as $|\mathbf r|\to\infty$ with $z>0$, uniformly in direction.
--
--   Together, 1-4 say that $\mathbf E^{\rm tot}$ is a radiating solution of the PEC bump problem (such a solution is classically unique), hence the exact reference solution used to validate the windowed MFIE-MoM in Section VII-A.
--
--   **Formalization Note** The Mie fields are characterised as the unique scattered fields of the PEC sphere: $C^2$ outside the sphere, continuous up to it, with $\nabla\times\nabla\times\mathbf E=k^2\mathbf E$, the PEC condition, and the Silver-Müller radiation condition in its electric-field form. They are not given as series. The bump is taken centred at the origin, as the image construction requires; the paper leaves the centre implicit. On the hemisphere, $\hat{\mathbf n}=\mathbf r/a$, so $\hat{\mathbf n}\times\mathbf E=\mathbf 0$ is written $\mathbf r\times\mathbf E=\mathbf 0$. On the planar part the rim $|\mathbf r|=a$ is included, where the conditions of parts 1 and 2 both apply.
-- source:
--   Arrieta and Pérez-Arancibia, Windowed Green Function MoM for Second-Kind Surface Integral Equation Formulations of Layered Media Electromagnetic Scattering Problems, arXiv:2210.02565v1 (2022), claim c021; Appendix A (Hemispherical bump problem: Mie series solution), PDF p. 11; setting of Section VII-A, PDF pp. 5-6; radiation condition eq. (3), Section II

import Mathlib
import Definitions.Def_Arxiv2210_02565_Basic

open Filter Topology

namespace Arxiv2210_02565

theorem hemispherical_bump_image_solution (k a : ℝ) (hk : 0 < k) (ha : 0 < a) (E0 : ℂ)
    (te : Bool) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ Real.pi / 2) :
    (∀ r : Space, r 2 = 0 → a ≤ ‖r‖ → crossProduct zhat (bumpTotalField k a E0 te α r) = 0) ∧
    (∀ r : Space, ‖r‖ = a → 0 ≤ r 2 → crossProduct (toC r) (bumpTotalField k a E0 te α r) = 0) ∧
    (∀ r : Space, 0 < r 2 → a < ‖r‖ →
      curl (curl (bumpTotalField k a E0 te α)) r = ((k : ℂ) ^ 2) • bumpTotalField k a E0 te α r) ∧
    Tendsto (fun r : Space => ((‖r‖ : ℝ) : ℂ) •
        (crossProduct (curl (bumpTotalField k a E0 te α - incAlpha k E0 te α - imageInc k E0 te α) r)
            (toC (‖r‖⁻¹ • r)) -
          (Complex.I * k) • (bumpTotalField k a E0 te α - incAlpha k E0 te α - imageInc k E0 te α) r))
      (Bornology.cobounded Space ⊓ 𝓟 {r : Space | 0 < r 2}) (𝓝 0) := by sorry

end Arxiv2210_02565
