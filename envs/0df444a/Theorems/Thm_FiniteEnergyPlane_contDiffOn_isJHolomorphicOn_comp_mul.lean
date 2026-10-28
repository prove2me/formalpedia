-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_isJHolomorphicOn_comp_mul
-- name    : FiniteEnergyPlane.contDiffOn_isJHolomorphicOn_comp_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T21:14:34.135261+00:00
-- url     : https://prove2.me/theorems/dc62d3f6-65cd-4b6f-9ea8-1db47fd9c758
-- title:
--   Energy and pseudoholomorphicity under dilation of a punctured disc
-- statement:
--   Let $E$ be a real normed space, $J:E\to\mathrm{End}(E)$, $\rho>0$, and let $v$ be $C^\infty$ and $J$-holomorphic on the punctured disc $\{0<|z|<\rho\}$. Put $w(z)=v(\rho z)$. Then $w$ is $C^\infty$ and $J$-holomorphic on the punctured unit disc $\{0<|z|<1\}$, $Dw(z)=\rho\,Dv(\rho z)$ for every $z\in\mathbb{C}$, and
--   $$\int_{0<|z|<1}\|Dw(z)\|^2\,dz=\int_{0<|z|<\rho}\|Dv(z)\|^2\,dz .$$
--
--   The Dirichlet energy and the $J$-holomorphic equation are invariant under dilation of the domain, so statements about punctured unit discs apply to punctured discs of any radius.
--
--   **Formalization Note** The dilation is `fun z => v ((ρ : ℂ) * z)`. The energies are lower integrals in `ℝ≥0∞` of the squared operator norm of `fderiv ℝ`. The derivative identity holds for all `z`, not only on the punctured disc.
-- source:
--   A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Section 4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Dilation of a punctured disc. Let `ρ > 0` and let `v` be smooth and `J`-holomorphic on the
punctured disc of radius `ρ`. Then `w z = v (ρ z)` is smooth and `J`-holomorphic on the punctured
unit disc, `Dw(z) = ρ Dv(ρ z)` for every `z`, and `w` on the punctured unit disc has the same
Dirichlet energy `∫ ‖D·‖²` as `v` on the punctured disc of radius `ρ`. -/
theorem contDiffOn_isJHolomorphicOn_comp_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : E → E →L[ℝ] E) (ρ : ℝ) (hρ : 0 < ρ) (v : ℂ → E)
    (hv : ContDiffOn ℝ ∞ v (ball 0 ρ \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 ρ \ {0}) v) :
    ContDiffOn ℝ ∞ (fun z => v ((ρ : ℂ) * z)) (ball 0 1 \ {0}) ∧
      JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) (fun z => v ((ρ : ℂ) * z)) ∧
      (∀ z, fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z = ρ • fderiv ℝ v ((ρ : ℂ) * z)) ∧
      ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z‖ ^ 2) =
        ∫⁻ z in ball 0 ρ \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) := by
  sorry

end FiniteEnergyPlane
