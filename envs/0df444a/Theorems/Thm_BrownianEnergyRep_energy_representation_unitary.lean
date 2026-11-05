-- Prove2me | Theorems.Thm_BrownianEnergyRep_energy_representation_unitary
-- name    : BrownianEnergyRep.energy_representation_unitary
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:06:15.466763+00:00
-- url     : https://prove2.me/theorems/11abcd9e-758d-44ca-b0db-cd4befc3345a
-- title:
--   The energy representation is a unitary representation (corrected: $E$)
-- statement:
--   With $E$ as corrected, the operators $E_\varphi$, $\varphi\in H(G)$, are unitary on $L^2(W(\mathfrak g),\nu)$, with
--   $$
--   E_\varphi^*=E_{\varphi^{-1}},\qquad E_\varphi E_\psi=E_{\varphi\psi} .
--   $$
--   For $\varphi,\psi\in H(G)$, the rotation $O_\varphi$ is a bounded linear map of $W(\mathfrak g)$ that preserves $\nu$, and $O_\varphi O_\psi=O_{\varphi\psi}$. So $E$ is a unitary representation of $H(G)$.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: O_ϕ(w) = ∫₀^· Ad_ϕ δw_s → pathwise by parts: Ad_{ϕ_t}w_t − ∫₀ᵗ Ad_{ϕ_s}[ϕ⁻¹ϕ′(s),w_s]ds; reason: ϕ is absolutely continuous; this equals the stochastic integral ν-a.e. and is defined for every w
--   - encoding: the integral ∫₀ᵀ⟨a,dw_s⟩ → the L²(ν) limit along step functions, as a representative chosen by Classical.epsilon; reason: it is unique ν-a.e. by wiener_integral_isometry
--   - encoding: operators defined by formulas on L² → unitary operators asserted to exist with these a.e. formulas on H(G); reason: f∘R_ϕ of an a.e. class is meaningful by quasi-invariance, and the formula determines the operator
--   - correction: Definition 5.7: phase coefficient 1, exp(i∫⟨ϕ⁻¹ϕ′,dw⟩) → coefficient 1/2; reason: on G = SO(2), T = 1, with ϕ_n = exp(θ_n J) and θ_n′ orthonormal, ‖N⁻¹Σ E_{ϕ_n}ξ‖² → e⁻¹‖ξ‖² for every ξ, while ‖N⁻¹Σ U^R_{ϕ_n}1‖² → e^{−1/4}, so the printed E is not equivalent to U^R; Proposition 5.5 itself produces 1/2
--   - correction: Definition 5.7: integrand ϕ⁻¹ϕ′ → integrand ϕ′ϕ⁻¹; reason: on G = SO(3), ϕ = exp(tA), ψ = exp(tB) in different planes, the integrands of E_ϕE_ψ1 and E_{ϕψ}1 differ by (t²/2)([A,[A,B]]+[B,[A,B]]) + O(t³) ≠ 0, so the printed E is not a homomorphism, while (ϕψ)′(ϕψ)⁻¹ = ϕ′ϕ⁻¹ + Ad_ϕ(ψ′ψ⁻¹) is the cocycle
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, p.18 (corrected)

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_IsGaussianWienerMeasure
import Definitions.Def_BrownianEnergyRep_rotation__ef917c
import Definitions.Def_BrownianEnergyRep_IsEnergyRep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The energy representation is a unitary representation of `H(G)` (arXiv:1511.07378v1, p.18), corrected:
`E_ϕ` is unitary, `E*_ϕ = E_{ϕ⁻¹}`, `E_ϕE_ψ = E_{ϕψ}`. Also `O_ϕ` is bounded linear, preserves `ν`, and `O_ϕO_ψ = O_{ϕψ}`. -/
theorem energy_representation_unitary {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G]
    [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (ν : Measure ↥(WienerPath E T)) (hν : IsGaussianWienerMeasure E T ν) :
    (∃ En, IsEnergyRep L ν En) ∧
    (∀ En, IsEnergyRep L ν En → ∀ ϕ ∈ FiniteEnergy L T,
      (En ϕ).symm = En ϕ⁻¹ ∧
      ContinuousLinearMap.adjoint ((En ϕ).toContinuousLinearEquiv : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) =
        ((En ϕ⁻¹).toContinuousLinearEquiv : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) ∧
      ∀ ψ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 ν, En ϕ (En ψ f) = En (ϕ * ψ) f) ∧
    ∀ ϕ ∈ FiniteEnergy L T,
      (∃ O : ↥(WienerPath E T) →L[ℝ] ↥(WienerPath E T), ⇑O = rotation L ϕ) ∧
      ν.map (rotation L ϕ) = ν ∧
      ∀ ψ ∈ FiniteEnergy L T, ∀ w, rotation L ϕ (rotation L ψ w) = rotation L (ϕ * ψ) w := by sorry

end BrownianEnergyRep
