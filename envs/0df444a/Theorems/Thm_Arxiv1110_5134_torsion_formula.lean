-- Prove2me | Theorems.Thm_Arxiv1110_5134_torsion_formula
-- name    : Arxiv1110_5134.torsion_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:18:37.042779+00:00
-- url     : https://prove2.me/theorems/c619c84b-95a1-432c-a420-05481326b86f
-- title:
--   Eqs. (46)-(47): the torsion of a ray from the refractive-index gradient
-- statement:
--   Let $n:\mathbb R^3\to\mathbb R$ be positive and twice continuously differentiable. Let $\mathbf r(s)$ be a ray parametrised by arc length with unit tangent $\boldsymbol\Omega(s)$, obeying the ray equation $\frac{d}{ds}(n\boldsymbol\Omega)=\nabla n$. At a point where $\boldsymbol\Omega\times\nabla n\ne0$:
--
--   - the curvature is $K=|\boldsymbol\Omega\times\nabla n/n|$;
--   - the principal normal is $\boldsymbol\nu=(\boldsymbol\delta-\boldsymbol\Omega\boldsymbol\Omega)\cdot\nabla n/(Kn)$;
--   - the binormal is $\mathbf b=(\boldsymbol\Omega\times\nabla n/n)/K$;
--   - the torsion $\kappa=-\mathbf b\cdot\partial\boldsymbol\nu/\partial s$ of Eq. (46) equals (Eq. 47)
--
--   $$\kappa=\frac{\boldsymbol\Omega\times\nabla n}{|\boldsymbol\Omega\times\nabla n|}\cdot\frac{\partial}{\partial s}\Big[\frac{(\boldsymbol\Omega\boldsymbol\Omega-\boldsymbol\delta)\cdot\nabla n}{|\boldsymbol\Omega\times\nabla n|}\Big].$$
--
--   **Formalization Note** The derivative $\partial/\partial s$ is the derivative along the ray, which is what the streaming operator gives when it acts on a quantity evaluated along the ray. The Frenet frame is $\boldsymbol\nu=K^{-1}d\boldsymbol\Omega/ds$ and $\mathbf b=\boldsymbol\Omega\times\boldsymbol\nu$, and the torsion has the sign of Eq. (46).
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c027; Section 4.2.2, Eqs. (46)-(47), PDF p. 20

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem torsion_formula (n : Vec3 → ℝ) (hn : ContDiff ℝ 2 n) (hpos : ∀ x, 0 < n x)
    (γ Ω : ℝ → Vec3) (hγ : ∀ t, HasDerivAt γ (Ω t) t) (hunit : ∀ t, Ω t ⬝ᵥ Ω t = 1)
    (hray : ∀ t, HasDerivAt (fun u => n (γ u) • Ω u) (cartGrad n (γ t)) t)
    (s : ℝ) (hK : Ω s ⨯₃ cartGrad n (γ s) ≠ 0) :
    rayCurvature Ω s = vlen (Ω s ⨯₃ cartGrad n (γ s)) / n (γ s) ∧
    frenetNormal Ω s = (vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ •
      (cartGrad n (γ s) - (Ω s ⬝ᵥ cartGrad n (γ s)) • Ω s) ∧
    frenetBinormal Ω s = (vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ • (Ω s ⨯₃ cartGrad n (γ s)) ∧
    rayTorsion Ω s =
      ((vlen (Ω s ⨯₃ cartGrad n (γ s)))⁻¹ • (Ω s ⨯₃ cartGrad n (γ s))) ⬝ᵥ
        deriv (fun u => (vlen (Ω u ⨯₃ cartGrad n (γ u)))⁻¹ •
          ((Ω u ⬝ᵥ cartGrad n (γ u)) • Ω u - cartGrad n (γ u))) s := by sorry

end Arxiv1110_5134
