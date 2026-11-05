-- Prove2me | Theorems.Thm_BrownianEnergyRep_proposition_5_5
-- name    : BrownianEnergyRep.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:03:30.582877+00:00
-- url     : https://prove2.me/theorems/c690aedb-e960-4520-972f-d6ea332c81f7
-- title:
--   Proposition 5.5 — $\mathcal F$ conjugates $U_{R,h}$ (corrected: sign, inverse, $h\in H$)
-- statement:
--   Let $(H,W,\Gamma)$ be an abstract Wiener space with $\mathcal F$ its Fourier-Wiener transform. For $f\in L^2(W,\Gamma)$, $R\in O(W^*)$ and $h\in H$, the operator $U_{R,h}$ is unitary and
--   $$
--   \big(\mathcal FU_{R,h}\mathcal F^{-1}f\big)(w)=e^{\frac i2\langle h,w\rangle}f\big((R^*)^{-1}w\big)\quad\text{for a.e. }w\in W .
--   $$
--   This turns the affine action into a phase and a rotation, which is the form of the energy representation.
--
--   Differences from the source:
--   - reading: R a topological homeomorphism of W* with adjoint R*: W → W → R orthogonal on H with a bounded bijection R* of W such that R*j = jR; reason: R* is defined on all of W only if the homeomorphism is weak-*; R*j = jR is the defining identity tested on j(H)
--   - encoding: F by Definition 17 of Driver-Hall, with a heuristic integral formula → the unitary with Fϕ̂ = e^{−|ϕ|²}e^{−⟨ϕ,·⟩}, the second identity of (5.2); reason: both families are total with Gram matrix exp(−½|ϕ−ψ|²), so this determines F
--   - encoding: ⟨h,w⟩ for h ∈ H → the L²(Γ) limit, as a representative chosen by Classical.epsilon (pairing); reason: unique a.e. by pairing_isometry
--   - correction: (5.1): e^{⟨h,w⟩−|h|²/2}f((R*)⁻¹(w−h)) → e^{⟨h,w⟩/2−|h|²/4}f((R*)⁻¹(w−h)); reason: with the printed factor and f = 1 the norm² is e^{|h|²} ≠ 1, so U is not unitary; the first two lines of (5.1) and the proof of Proposition 5.5 take the square root
--   - correction: e^{−i⟨h,w⟩/2}f(R*w) → e^{+i⟨h,w⟩/2}f((R*)⁻¹w); reason: the last line of the printed proof has +i; with h = 0 and f = ϕ̂, F commutes with U_{R,0} and gives ϕ̂∘(R*)⁻¹, not ϕ̂∘R*, whenever R² ≠ I
--   - generalization: h ∈ W* → h ∈ H; reason: the goal needs it, because for finite-energy ϕ the path h = −∫ϕ′ϕ⁻¹ need not be in W*; W* ⊂ H
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Proposition 5.5, p.17 (corrected)

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace_pairing
import Definitions.Def_BrownianEnergyRep_Rotation
import Definitions.Def_BrownianEnergyRep_IsFourierWiener
import Definitions.Def_BrownianEnergyRep_IsGaussianRegularRep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Proposition 5.5 (arXiv:1511.07378v1, p.17), corrected:
`(F U_{R,h} F⁻¹ f)(w) = e^{(i/2)⟨h,w⟩} f((R*)⁻¹ w)`, for `h ∈ H`. -/
theorem proposition_5_5 {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    (A : AbstractWienerSpace H W) (F : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 A.Γ)
    (hF : IsFourierWiener A F) (ρ : Rotation A) (h : H) :
    ∃ U, IsGaussianRegularRep A ρ h U ∧ ∀ f : Lp ℂ 2 A.Γ,
      (F (U (F.symm f)) : W → ℂ) =ᵐ[A.Γ]
        fun w => Complex.exp (Complex.I / 2 * (A.pairing h w : ℂ)) * f (ρ.adj.symm w) := by sorry

end BrownianEnergyRep
