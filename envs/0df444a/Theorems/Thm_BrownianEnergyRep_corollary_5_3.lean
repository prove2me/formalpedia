-- Prove2me | Theorems.Thm_BrownianEnergyRep_corollary_5_3
-- name    : BrownianEnergyRep.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:02:05.993281+00:00
-- url     : https://prove2.me/theorems/bfc335e7-7ab8-4165-b980-79364a9c8855
-- title:
--   Corollary 5.3 — a rotation extends to a unitary of $L^2(W,\Gamma)$
-- statement:
--   Any $R\in O(W^*)$ extends to a unitary map on $L^2(W,\Gamma)$: the map $f\mapsto f\circ(R^*)^{-1}$ is unitary and sends $\langle h,\cdot\rangle$ to $\langle Rh,\cdot\rangle$ for every $h\in H$.
--
--   Differences from the source:
--   - reading: R a topological homeomorphism of W* with adjoint R*: W → W → R orthogonal on H with a bounded bijection R* of W such that R*j = jR; reason: R* is defined on all of W only if the homeomorphism is weak-*; R*j = jR is the defining identity tested on j(H)
--   - encoding: ⟨h,w⟩ for h ∈ H → the L²(Γ) limit, as a representative chosen by Classical.epsilon (pairing); reason: unique a.e. by pairing_isometry
--   - encoding: "extends to a unitary map" → the unitary f ↦ f∘(R*)⁻¹, which maps ⟨h,·⟩ to ⟨Rh,·⟩; reason: H sits in L²(W,Γ) by h ↦ ⟨h,·⟩, and this is the extension (5.1) uses
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Corollary 5.3, p.16

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace_pairing
import Definitions.Def_BrownianEnergyRep_Rotation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Corollary 5.3 (arXiv:1511.07378v1, p.16): `R` extends to a unitary map of `L²(W, Γ)`.

**Formalization Note** The unitary is `f ↦ f ∘ (R*)⁻¹`, and it extends `R` in that it sends `⟨h,·⟩` to
`⟨Rh,·⟩`. The two `MemLp` hypotheses hold for every `h`. -/
theorem corollary_5_3 {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    (A : AbstractWienerSpace H W) (ρ : Rotation A) :
    ∃ U : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 A.Γ,
      (∀ f : Lp ℂ 2 A.Γ, (U f : W → ℂ) =ᵐ[A.Γ] fun w => f (ρ.adj.symm w)) ∧
      ∀ (h : H) (h₁ : MemLp (fun w => (A.pairing h w : ℂ)) 2 A.Γ)
        (h₂ : MemLp (fun w => (A.pairing (ρ.R h) w : ℂ)) 2 A.Γ),
        U (h₁.toLp _) = h₂.toLp _ := by sorry

end BrownianEnergyRep
