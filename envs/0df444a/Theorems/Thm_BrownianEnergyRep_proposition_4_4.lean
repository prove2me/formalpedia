-- Prove2me | Theorems.Thm_BrownianEnergyRep_proposition_4_4
-- name    : BrownianEnergyRep.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:05:04.15906+00:00
-- url     : https://prove2.me/theorems/6fb1dc19-89c6-4678-8475-15daae7af9bd
-- title:
--   Proposition 4.4 — $U^R$, $U^L$ are unitary representations (corrected: density index order)
-- statement:
--   The formulas of Definition 4.1 define unitary operators on $L^2(W(G),\mu)$. For $\varphi_1,\dots,\varphi_n,\psi_1,\dots,\psi_n\in H(G)$ and $f\in L^2(W(G),\mu)$,
--   $$
--   (U^R_{\varphi_1}\cdots U^R_{\varphi_n}f)(g)=\big(Z^R_{\varphi_1\cdots\varphi_n}\big)^{1/2}(g)\,f(R_{\varphi_1\cdots\varphi_n}g),
--   $$
--   $$
--   (U^L_{\psi_1}\cdots U^L_{\psi_n}f)(g)=\big(Z^L_{\psi_1\cdots\psi_n}\big)^{1/2}(g)\,f(L_{\psi_1\cdots\psi_n}g),
--   $$
--   and
--   $$
--   (U^R_\varphi)^{-1}=(U^R_\varphi)^*=U^R_{\varphi^{-1}},\qquad(U^L_\psi)^{-1}=(U^L_\psi)^*=U^L_{\psi^{-1}} .
--   $$
--   So $U^R$ and $U^L$ are unitary representations of $H(G)$.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: Z^R_ϕ, Z^L_ϕ the densities of Theorem 2.14 → rnDeriv of the laws of g ↦ gϕ⁻¹ and g ↦ ϕg with respect to μ; reason: this is what ∫F(gϕ)Z^R dμ = ∫F dμ = ∫F(ϕ⁻¹g)Z^L dμ says; theorem_2_14 identifies them with the printed exponentials
--   - encoding: operators defined by formulas on L² → unitary operators asserted to exist with these a.e. formulas on H(G); reason: f∘R_ϕ of an a.e. class is meaningful by quasi-invariance, and the formula determines the operator
--   - correction: density index Z^R_{ϕₙ…ϕ₁}, Z^L_{ψₙ…ψ₁} → Z^R_{ϕ₁…ϕₙ}, Z^L_{ψ₁…ψₙ}; reason: Theorem 2.14 gives Z_{ϕ₁}(g)Z_{ϕ₂}(gϕ₁) = Z_{ϕ₁ϕ₂}(g); with f = 1 and non-commuting ϕ₁, ϕ₂ (the SO(3) pair) the printed index gives a different density, by the injectivity of Proposition 4.3
--   - generalization: ϕ₁,…,ϕₙ with n ≥ 1 → a list, possibly empty; reason: the empty product is the identity; the case n ≥ 1 is the printed one
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Proposition 4.4, p.13 (corrected)

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

/-- Proposition 4.4 (arXiv:1511.07378v1, p.13), corrected: the density of a product carries the order of the
composition, `Z^R_{ϕ₁…ϕₙ}`, not `Z^R_{ϕₙ…ϕ₁}`.

**Formalization Note** `l.foldr` is the composition `U_{ϕ₁} … U_{ϕₙ}` and `l.prod = ϕ₁…ϕₙ`. -/
theorem proposition_4_4 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G]
    [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ) :
    (∃ U, IsRightBrownianRep L μ U) ∧ (∃ U, IsLeftBrownianRep L μ U) ∧
    ∀ UR UL, IsRightBrownianRep L μ UR → IsLeftBrownianRep L μ UL →
      (∀ l : List ↥(WienerGroup G T), (∀ ϕ ∈ l, ϕ ∈ FiniteEnergy L T) → ∀ f : Lp ℂ 2 μ,
        (l.foldr (fun ϕ (acc : Lp ℂ 2 μ) => UR ϕ acc) f : Lp ℂ 2 μ) =ᵐ[μ]
          fun g => (Real.sqrt (densityR μ l.prod g).toReal : ℂ) * f (g * l.prod)) ∧
      (∀ l : List ↥(WienerGroup G T), (∀ ψ ∈ l, ψ ∈ FiniteEnergy L T) → ∀ f : Lp ℂ 2 μ,
        (l.foldr (fun ψ (acc : Lp ℂ 2 μ) => UL ψ acc) f : Lp ℂ 2 μ) =ᵐ[μ]
          fun g => (Real.sqrt (densityL μ l.prod g).toReal : ℂ) * f (l.prod⁻¹ * g)) ∧
      ∀ ϕ ∈ FiniteEnergy L T,
        (UR ϕ).symm = UR ϕ⁻¹ ∧
        ContinuousLinearMap.adjoint ((UR ϕ).toContinuousLinearEquiv : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) =
          ((UR ϕ⁻¹).toContinuousLinearEquiv : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) ∧
        (UL ϕ).symm = UL ϕ⁻¹ ∧
        ContinuousLinearMap.adjoint ((UL ϕ).toContinuousLinearEquiv : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) =
          ((UL ϕ⁻¹).toContinuousLinearEquiv : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by sorry

end BrownianEnergyRep
