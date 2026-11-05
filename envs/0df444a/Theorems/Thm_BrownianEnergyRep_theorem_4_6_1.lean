-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_4_6_1
-- name    : BrownianEnergyRep.theorem_4_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:04:53.576033+00:00
-- url     : https://prove2.me/theorems/6f6ed36e-f696-46d9-a76e-8b1486394c4f
-- title:
--   Theorem 4.6(1) — $U^R$ and $U^L$ commute and $J$ intertwines them
-- statement:
--   The unitary operators $U^R_\varphi$ and $U^L_\psi$ commute for all $\varphi,\psi\in H(G)$, so that
--   $$
--   \mathcal M^L\subseteq(\mathcal M^R)',\qquad\mathcal M^R\subseteq(\mathcal M^L)' .
--   $$
--   The representations $U^L$ and $U^R$ are unitarily equivalent, and the intertwining operator is the unitary involution $J$ of (2.12): $JU^R_\varphi=U^L_\varphi J$.
--
--   This reduces the main theorem for $U^L$ to the one for $U^R$.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: Z^R_ϕ, Z^L_ϕ the densities of Theorem 2.14 → rnDeriv of the laws of g ↦ gϕ⁻¹ and g ↦ ϕg with respect to μ; reason: this is what ∫F(gϕ)Z^R dμ = ∫F dμ = ∫F(ϕ⁻¹g)Z^L dμ says; theorem_2_14 identifies them with the printed exponentials
--   - encoding: operators defined by formulas on L² → unitary operators asserted to exist with these a.e. formulas on H(G); reason: f∘R_ϕ of an a.e. class is meaningful by quasi-invariance, and the formula determines the operator
--   - reading: (𝓜^R)′ ⊆ 𝓜^L and (𝓜^L)′ ⊆ 𝓜^R, "and so" from commutation → 𝓜^L ⊆ (𝓜^R)′ and 𝓜^R ⊆ (𝓜^L)′; reason: commutation yields only these; the proof of clause 3 (p.15) uses that T ∈ 𝓜^R commutes with 𝓜^L; and the printed direction would, with commutation, make the algebras each other's commutants, which p.14 says Theorem 4.6 does not answer
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 4.6(1), p.14; Notation 4.5, p.13

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_IsRightBrownianRep
import Definitions.Def_BrownianEnergyRep_IsLeftBrownianRep
import Definitions.Def_BrownianEnergyRep_IsInversionOperator
import Definitions.Def_BrownianEnergyRep_generatedVonNeumann

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 4.6(1) (arXiv:1511.07378v1, p.14): `U^R` and `U^L` commute, and the involution `J` intertwines them.

**Formalization Note** The page prints `(𝓜^R)′ ⊆ 𝓜^L` and `(𝓜^L)′ ⊆ 𝓜^R`. Commutation gives the inclusions
stated here, `𝓜^L ⊆ (𝓜^R)′` and `𝓜^R ⊆ (𝓜^L)′`; the printed ones would, with commutation, say that the
two algebras are each other's commutants, which p.14 says the theorem does not answer. -/
theorem theorem_4_6_1 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (UR UL : ↥(WienerGroup G T) → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ))
    (hUR : IsRightBrownianRep L μ UR) (hUL : IsLeftBrownianRep L μ UL) :
    (∀ ϕ ∈ FiniteEnergy L T, ∀ ψ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 μ,
      UR ϕ (UL ψ f) = UL ψ (UR ϕ f)) ∧
    generatedVonNeumann L UL ⊆ Set.centralizer (generatedVonNeumann L UR) ∧
    generatedVonNeumann L UR ⊆ Set.centralizer (generatedVonNeumann L UL) ∧
    ∃ J, IsInversionOperator μ J ∧ (∀ f, J (J f) = f) ∧
      ∀ ϕ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 μ, J (UR ϕ f) = UL ϕ (J f) := by sorry

end BrownianEnergyRep
