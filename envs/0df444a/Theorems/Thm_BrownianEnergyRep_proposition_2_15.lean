-- Prove2me | Theorems.Thm_BrownianEnergyRep_proposition_2_15
-- name    : BrownianEnergyRep.proposition_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:05:08.62766+00:00
-- url     : https://prove2.me/theorems/b40e14c5-ad72-4d2f-856a-798f3b13bbc9
-- title:
--   Proposition 2.15 — $Z^R_\varphi=Z^L_\varphi\circ\Theta$
-- statement:
--   For $\varphi\in H(G)$, the left and right Radon-Nikodym densities satisfy
--   $$
--   Z^R_\varphi=JZ^L_\varphi=Z^L_\varphi\circ\Theta\quad\text{for }\mu\text{-almost every }g .
--   $$
--   This is what lets $J$ intertwine the two Brownian representations.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: Z^R_ϕ, Z^L_ϕ the densities of Theorem 2.14 → rnDeriv of the laws of g ↦ gϕ⁻¹ and g ↦ ϕg with respect to μ; reason: this is what ∫F(gϕ)Z^R dμ = ∫F dμ = ∫F(ϕ⁻¹g)Z^L dμ says; theorem_2_14 identifies them with the printed exponentials
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Proposition 2.15, p.10

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_IsRightBrownianRep
import Definitions.Def_BrownianEnergyRep_IsLeftBrownianRep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Proposition 2.15 (arXiv:1511.07378v1, p.10): `Z^R_ϕ = Z^L_ϕ ∘ Θ` for `μ`-almost every `g`. -/
theorem proposition_2_15 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G]
    [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (ϕ : ↥(WienerGroup G T)) (hϕ : ϕ ∈ FiniteEnergy L T) :
    densityR μ ϕ =ᵐ[μ] fun γ => densityL μ ϕ γ⁻¹ := by sorry

end BrownianEnergyRep
