-- Prove2me | Theorems.Thm_BrownianEnergyRep_proposition_2_13
-- name    : BrownianEnergyRep.proposition_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:58.238207+00:00
-- url     : https://prove2.me/theorems/3115e7c7-9106-4b74-a678-1f352f8c480c
-- title:
--   Proposition 2.13 — the Itô maps are measure-preserving isomorphisms
-- statement:
--   The maps $B^L,B^R:(W(G),\mu)\to(W(\mathfrak g),\nu)$ are $\mu$-a.e. defined maps with $B^L_*\mu=\nu=B^R_*\mu$. They are measure-preserving isomorphisms, with inverses given by solving the Stratonovich equations
--   $$
--   \delta w=w\,\delta B^L\quad\text{or}\quad\delta w=\delta B^R\,w,\qquad w_0=e .
--   $$
--   Moreover,
--   $$
--   B^L\circ\Theta=-B^R\ \text{ a.e.}\quad\text{and}\quad B^R\circ\Theta=-B^L\ \text{ a.e.},\tag{2.7}
--   $$
--   and $\mu$ is invariant under the inversion $\Theta$. Thus $L^2(W(G),\mu)$ and $L^2(W(\mathfrak g),\nu)$ are unitarily identified.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: Stratonovich and Itô integrals against semimartingales → limits in probability of trapezoidal and left-point sums along every partition sequence with mesh → 0, entrywise for matrices; reason: these are the standard characterizations of the integrals
--   - encoding: B^L, B^R μ-a.e. defined maps → AEMeasurable maps W(G) → W(𝔤) that satisfy the limit predicates; reason: such a map is determined μ-a.e. by the predicates and path continuity
--   - encoding: measure-preserving isomorphism with inverse maps → an a.e. measurable Φ with Φ_*ν = μ, Φ∘B = id μ-a.e., B∘Φ = id ν-a.e.; reason: this is the definition of an isomorphism modulo null sets
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Proposition 2.13, p.7; p.9

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_IsGaussianWienerMeasure
import Definitions.Def_BrownianEnergyRep_IsLeftItoMap
import Definitions.Def_BrownianEnergyRep_IsRightItoMap
import Definitions.Def_BrownianEnergyRep_IsLeftSDESolution
import Definitions.Def_BrownianEnergyRep_IsRightSDESolution

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Proposition 2.13 (arXiv:1511.07378v1, p.7): the Itô maps are measure-preserving isomorphisms whose inverses
solve the SDEs, and (2.7). The last clause is the invariance of `μ` under inversion (p.9). -/
theorem proposition_2_13 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G]
    [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (ν : Measure ↥(WienerPath E T)) (hν : IsGaussianWienerMeasure E T ν)
    (BL BR : ↥(WienerGroup G T) → ↥(WienerPath E T))
    (hBL : IsLeftItoMap L μ BL) (hBR : IsRightItoMap L μ BR) :
    μ.map BL = ν ∧ μ.map BR = ν ∧
    (∃ Φ : ↥(WienerPath E T) → ↥(WienerGroup G T), AEMeasurable Φ ν ∧ ν.map Φ = μ ∧
      (∀ᵐ γ ∂μ, Φ (BL γ) = γ) ∧ (∀ᵐ w ∂ν, BL (Φ w) = w) ∧ IsLeftSDESolution L ν Φ) ∧
    (∃ Φ : ↥(WienerPath E T) → ↥(WienerGroup G T), AEMeasurable Φ ν ∧ ν.map Φ = μ ∧
      (∀ᵐ γ ∂μ, Φ (BR γ) = γ) ∧ (∀ᵐ w ∂ν, BR (Φ w) = w) ∧ IsRightSDESolution L ν Φ) ∧
    (∀ᵐ γ ∂μ, BL γ⁻¹ = -BR γ) ∧ (∀ᵐ γ ∂μ, BR γ⁻¹ = -BL γ) ∧
    μ.map (fun γ => γ⁻¹) = μ := by sorry

end BrownianEnergyRep
