-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_5_8
-- name    : BrownianEnergyRep.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:06:23.489673+00:00
-- url     : https://prove2.me/theorems/7180e2fc-c372-463e-b90d-675a6561f451
-- title:
--   Theorem 5.8 — $U^R$ and $U^L$ are unitarily equivalent to the energy representation (corrected: phase $\frac i2\int\langle\varphi'\varphi^{-1},dw\rangle$ in $E$)
-- statement:
--   Let $G$ be a compact connected subgroup of $\mathrm{GL}_n(\mathbb R)$, $\mathfrak g$ its Lie algebra with an $\mathrm{Ad}_G$-invariant inner product, and $0<T<\infty$. Let $\mu$ be the Wiener measure on $W(G)$ and $\nu$ the Wiener measure on $W(\mathfrak g)$. Then the right and left Brownian measure representations $U^R$, $U^L$ of the finite energy group $H(G)$ on $L^2(W(G),\mu)$ and the energy representation
--   $$
--   (E_\varphi f)(w)=\exp\Big(\frac i2\int_0^T\langle\varphi'\varphi^{-1}(s),dw_s\rangle\Big)f\big(O_{\varphi^{-1}}w\big)
--   $$
--   on $L^2(W(\mathfrak g),\nu)$ are unitary representations, and there are unitaries $V_R,V_L:L^2(W(G),\mu)\to L^2(W(\mathfrak g),\nu)$ such that, for all $\varphi\in H(G)$,
--   $$
--   V_RU^R_\varphi=E_\varphi V_R,\qquad V_LU^L_\varphi=E_\varphi V_L .
--   $$
--   This identifies two representations of the path group: one on a curved path space and one on a linear path space.
--
--   **Formalization Note** One $V_R$ and one $V_L$ serve all $\varphi$.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: Borel σ-algebra of the uniform metric d_∞ on W(G) → Borel σ-algebra of the compact-open topology; reason: the two topologies agree because G is compact
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: Z^R_ϕ, Z^L_ϕ the densities of Theorem 2.14 → rnDeriv of the laws of g ↦ gϕ⁻¹ and g ↦ ϕg with respect to μ; reason: this is what ∫F(gϕ)Z^R dμ = ∫F dμ = ∫F(ϕ⁻¹g)Z^L dμ says; theorem_2_14 identifies them with the printed exponentials
--   - encoding: O_ϕ(w) = ∫₀^· Ad_ϕ δw_s → pathwise by parts: Ad_{ϕ_t}w_t − ∫₀ᵗ Ad_{ϕ_s}[ϕ⁻¹ϕ′(s),w_s]ds; reason: ϕ is absolutely continuous; this equals the stochastic integral ν-a.e. and is defined for every w
--   - encoding: the integral ∫₀ᵀ⟨a,dw_s⟩ → the L²(ν) limit along step functions, as a representative chosen by Classical.epsilon; reason: it is unique ν-a.e. by wiener_integral_isometry
--   - encoding: operators defined by formulas on L² → unitary operators asserted to exist with these a.e. formulas on H(G); reason: f∘R_ϕ of an a.e. class is meaningful by quasi-invariance, and the formula determines the operator
--   - correction: Definition 5.7: phase coefficient 1, exp(i∫⟨ϕ⁻¹ϕ′,dw⟩) → coefficient 1/2; reason: on G = SO(2), T = 1, with ϕ_n = exp(θ_n J) and θ_n′ orthonormal, ‖N⁻¹Σ E_{ϕ_n}ξ‖² → e⁻¹‖ξ‖² for every ξ, while ‖N⁻¹Σ U^R_{ϕ_n}1‖² → e^{−1/4}, so the printed E is not equivalent to U^R; Proposition 5.5 itself produces 1/2
--   - correction: Definition 5.7: integrand ϕ⁻¹ϕ′ → integrand ϕ′ϕ⁻¹; reason: on G = SO(3), ϕ = exp(tA), ψ = exp(tB) in different planes, the integrands of E_ϕE_ψ1 and E_{ϕψ}1 differ by (t²/2)([A,[A,B]]+[B,[A,B]]) + O(t³) ≠ 0, so the printed E is not a homomorphism, while (ϕψ)′(ϕψ)⁻¹ = ϕ′ϕ⁻¹ + Ad_ϕ(ψ′ψ⁻¹) is the cocycle
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 5.8, p.18; Definition 5.7, p.18 (corrected)

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
import Definitions.Def_BrownianEnergyRep_IsEnergyRep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 5.8 (arXiv:1511.07378v1, p.18), with Definition 5.7 corrected: both `U^R` and `U^L` are unitarily equivalent
to the energy representation `E`.

**Formalization Note** One `V_R` and one `V_L` serve every `ϕ ∈ H(G)`. The operators are asserted to
exist with their a.e. formulas (`IsRightBrownianRep`, `IsLeftBrownianRep`, `IsEnergyRep`), which
determine them on `H(G)`. `E` is corrected as in `IsEnergyRep`. -/
theorem theorem_5_8 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (ν : Measure ↥(WienerPath E T)) (hν : IsGaussianWienerMeasure E T ν) :
    ∃ (UR UL : ↥(WienerGroup G T) → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ))
      (En : ↥(WienerGroup G T) → (Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 ν))
      (VR VL : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν),
      IsRightBrownianRep L μ UR ∧ IsLeftBrownianRep L μ UL ∧ IsEnergyRep L ν En ∧
      ∀ ϕ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 μ,
        VR (UR ϕ f) = En ϕ (VR f) ∧ VL (UL ϕ f) = En ϕ (VL f) := by sorry

end BrownianEnergyRep
