-- Prove2me | Theorems.Thm_BrownianEnergyRep_theorem_2_10
-- name    : BrownianEnergyRep.theorem_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:04:56.31412+00:00
-- url     : https://prove2.me/theorems/8ae15daa-36e8-45bc-8dae-126591782922
-- title:
--   Theorem 2.10 — the Itô maps under translation
-- statement:
--   Let $\varphi\in H(G)$. The processes $B^L$ and $B^R$ are $\mathfrak g$-valued Brownian motions with
--   1. $dB^R_t=\mathrm{Ad}_{g_t}dB^L_t=\mathrm{Ad}_{g_t}\delta B^L_t$,
--   2. $dB^L_t=\mathrm{Ad}_{g_t^{-1}}dB^R_t=\mathrm{Ad}_{g_t^{-1}}\delta B^R_t$,
--   3. $B^L_t(\varphi^{-1}g)=B^L_t-\int_0^t\mathrm{Ad}_{g^{-1}}(\delta\varphi\,\varphi^{-1})$,
--   4. $B^L_t(g\varphi)=\int_0^t\mathrm{Ad}_{\varphi^{-1}}dB^L+\int_0^t\varphi^{-1}\delta\varphi$,
--   5. $B^R_t(\varphi^{-1}g)=-\int_0^t\varphi^{-1}\delta\varphi+\int_0^t\mathrm{Ad}_{\varphi^{-1}}\delta B^R$,
--   6. $B^R_t(g\varphi)=B^R_t+\int_0^t\mathrm{Ad}_g(\delta\varphi\,\varphi^{-1})$.
--
--   Clauses (3)-(6) hold for $\mu$-a.e. $g$. Clause (4) is what turns right translation into an affine map of $W(\mathfrak g)$.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: Stratonovich and Itô integrals against semimartingales → limits in probability of trapezoidal and left-point sums along every partition sequence with mesh → 0, entrywise for matrices; reason: these are the standard characterizations of the integrals
--   - encoding: B^L, B^R μ-a.e. defined maps → AEMeasurable maps W(G) → W(𝔤) that satisfy the limit predicates; reason: such a map is determined μ-a.e. by the predicates and path continuity
--   - encoding: O_ϕ(w) = ∫₀^· Ad_ϕ δw_s → pathwise by parts: Ad_{ϕ_t}w_t − ∫₀ᵗ Ad_{ϕ_s}[ϕ⁻¹ϕ′(s),w_s]ds; reason: ϕ is absolutely continuous; this equals the stochastic integral ν-a.e. and is defined for every w
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.10, p.6; (2.13), p.10

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_IsGaussianWienerMeasure
import Definitions.Def_BrownianEnergyRep_primitive
import Definitions.Def_BrownianEnergyRep_rotation__ef917c
import Definitions.Def_BrownianEnergyRep_TimeGrid
import Definitions.Def_BrownianEnergyRep_IsLeftItoMap
import Definitions.Def_BrownianEnergyRep_IsRightItoMap
import Definitions.Def_BrownianEnergyRep_adItoSum

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Theorem 2.10 (arXiv:1511.07378v1, p.6), clauses (1)-(6).

**Formalization Note** The integrals `∫ Ad_{ϕ⁻¹} dB` of (4), (5) have a deterministic integrand and are
`rotation L ϕ⁻¹ B`. Clauses (3)-(6) hold for `μ`-a.e. `g`. -/
theorem theorem_2_10 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (ν : Measure ↥(WienerPath E T)) (hν : IsGaussianWienerMeasure E T ν)
    (BL BR : ↥(WienerGroup G T) → ↥(WienerPath E T))
    (hBL : IsLeftItoMap L μ BL) (hBR : IsRightItoMap L μ BR)
    (ϕ : ↥(WienerGroup G T)) (hϕ : ϕ ∈ FiniteEnergy L T) :
    μ.map BL = ν ∧ μ.map BR = ν ∧
    (∀ t ∈ Icc 0 T, ∀ π : ℕ → TimeGrid t, Tendsto (fun j => (π j).mesh) atTop (𝓝 0) →
      TendstoInMeasure μ (fun j γ => adItoSum L (π j) γ (BL γ)) atTop (fun γ => wAt (BR γ) t) ∧
      TendstoInMeasure μ (fun j γ => adStratSum L (π j) γ (BL γ)) atTop
        (fun γ => wAt (BR γ) t)) ∧
    (∀ t ∈ Icc 0 T, ∀ π : ℕ → TimeGrid t, Tendsto (fun j => (π j).mesh) atTop (𝓝 0) →
      TendstoInMeasure μ (fun j γ => adItoSum L (π j) γ⁻¹ (BR γ)) atTop
        (fun γ => wAt (BL γ) t) ∧
      TendstoInMeasure μ (fun j γ => adStratSum L (π j) γ⁻¹ (BR γ)) atTop
        (fun γ => wAt (BL γ) t)) ∧
    (∀ᵐ γ ∂μ, BL (ϕ⁻¹ * γ) =
      BL γ - primitive T fun s => L.Ad (pathAt γ⁻¹ s) (rightLog L ϕ s)) ∧
    (∀ᵐ γ ∂μ, BL (γ * ϕ) = rotation L ϕ⁻¹ (BL γ) + primitive T (leftLog L ϕ)) ∧
    (∀ᵐ γ ∂μ, BR (ϕ⁻¹ * γ) = -primitive T (leftLog L ϕ) + rotation L ϕ⁻¹ (BR γ)) ∧
    (∀ᵐ γ ∂μ, BR (γ * ϕ) =
      BR γ + primitive T fun s => L.Ad (pathAt γ s) (rightLog L ϕ s)) := by sorry

end BrownianEnergyRep
