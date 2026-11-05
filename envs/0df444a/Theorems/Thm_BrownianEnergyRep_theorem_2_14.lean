-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_2_14
-- name    : BrownianEnergyRep.theorem_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:05:28.105259+00:00
-- url     : https://prove2.me/theorems/2716e09f-4821-4073-9429-2c241885ea5a
-- title:
--   Theorem 2.14 — quasi-invariance of $\mu$ with explicit densities
-- statement:
--   For $\varphi\in H(G)$, let
--   $$
--   Z^R_T(\varphi)=\exp\Big(-\int_0^T\langle\varphi'\varphi^{-1},\delta B^L\rangle-\frac12\int_0^T|\varphi'\varphi^{-1}|^2dt\Big),
--   $$
--   $$
--   Z^L_T(\varphi)=\exp\Big(\int_0^T\langle\varphi'\varphi^{-1},\delta B^R\rangle-\frac12\int_0^T|\varphi'\varphi^{-1}|^2dt\Big).
--   $$
--   Then, for every bounded measurable $F$ on $W(G)$,
--   $$
--   \int_{W(G)}F(g\varphi)Z^R_T(\varphi)\,d\mu=\int_{W(G)}F\,d\mu=\int_{W(G)}F(\varphi^{-1}g)Z^L_T(\varphi)\,d\mu .
--   $$
--   In particular $\mu$ is quasi-invariant under left and right translation by $H(G)$, and $Z^R_T(\varphi)$, $Z^L_T(\varphi)$ are the Radon-Nikodym densities $Z^R_\varphi$, $Z^L_\varphi$. This is the input that makes $U^R$ and $U^L$ unitary.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: B^L, B^R μ-a.e. defined maps → AEMeasurable maps W(G) → W(𝔤) that satisfy the limit predicates; reason: such a map is determined μ-a.e. by the predicates and path continuity
--   - encoding: the integral ∫₀ᵀ⟨a,dw_s⟩ → the L²(ν) limit along step functions, as a representative chosen by Classical.epsilon; reason: it is unique ν-a.e. by wiener_integral_isometry
--   - encoding: Z^R_ϕ, Z^L_ϕ the densities of Theorem 2.14 → rnDeriv of the laws of g ↦ gϕ⁻¹ and g ↦ ϕg with respect to μ; reason: this is what ∫F(gϕ)Z^R dμ = ∫F dμ = ∫F(ϕ⁻¹g)Z^L dμ says; theorem_2_14 identifies them with the printed exponentials
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.14, p.8; p.10

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_IsGaussianWienerMeasure
import Definitions.Def_BrownianEnergyRep_IsRightBrownianRep
import Definitions.Def_BrownianEnergyRep_IsLeftBrownianRep
import Definitions.Def_BrownianEnergyRep_IsLeftItoMap
import Definitions.Def_BrownianEnergyRep_IsRightItoMap
import Definitions.Def_BrownianEnergyRep_exponentialDensityR
import Definitions.Def_BrownianEnergyRep_exponentialDensityL

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 2.14 (arXiv:1511.07378v1, p.8): quasi-invariance with the printed explicit densities. -/
theorem theorem_2_14 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (ν : Measure ↥(WienerPath E T)) (hν : IsGaussianWienerMeasure E T ν)
    (BL BR : ↥(WienerGroup G T) → ↥(WienerPath E T))
    (hBL : IsLeftItoMap L μ BL) (hBR : IsRightItoMap L μ BR)
    (ϕ : ↥(WienerGroup G T)) (hϕ : ϕ ∈ FiniteEnergy L T) :
    (∀ F : ↥(WienerGroup G T) → ℝ, Measurable F → (∃ C, ∀ γ, |F γ| ≤ C) →
      ∫ γ, F (γ * ϕ) * exponentialDensityR L ν BL ϕ γ ∂μ = ∫ γ, F γ ∂μ ∧
      ∫ γ, F (ϕ⁻¹ * γ) * exponentialDensityL L ν BR ϕ γ ∂μ = ∫ γ, F γ ∂μ) ∧
    (μ.map (fun g => g * ϕ⁻¹)).AbsolutelyContinuous μ ∧
    μ.AbsolutelyContinuous (μ.map (fun g => g * ϕ⁻¹)) ∧
    (μ.map (fun g => ϕ * g)).AbsolutelyContinuous μ ∧
    μ.AbsolutelyContinuous (μ.map (fun g => ϕ * g)) ∧
    (fun γ => (densityR μ ϕ γ).toReal) =ᵐ[μ] exponentialDensityR L ν BL ϕ ∧
    (fun γ => (densityL μ ϕ γ).toReal) =ᵐ[μ] exponentialDensityL L ν BR ϕ := by sorry

end BrownianEnergyRep
