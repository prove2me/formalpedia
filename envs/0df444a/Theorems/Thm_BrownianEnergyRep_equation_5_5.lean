-- Prove2me | Theorems.Thm_BrownianEnergyRep_equation_5_5
-- name    : BrownianEnergyRep.equation_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:06:47.746404+00:00
-- url     : https://prove2.me/theorems/c4cdaa72-ed7c-4cc6-bd53-75150c8ef55b
-- title:
--   (5.5) and the intertwiners of Theorem 5.8 (corrected: phase, $R^*$, $h$, $\mathcal F^{-1}$)
-- statement:
--   Let $S=(B^L)^*$ be the unitary $f\mapsto f\circ B^L$ from $L^2(W(\mathfrak g),\nu)$ to $L^2(W(G),\mu)$. For $\varphi\in H(G)$, $U^R_\varphi$ corresponds under $S$ to the operator
--   $$
--   (u_\varphi f)(w)=\exp\Big(-\frac12\int_0^T\langle\varphi'\varphi^{-1}(s),dw_s\rangle-\frac14\|\varphi\|^2_{H,T}\Big)\,f\Big(O_{\varphi^{-1}}w+\int_0^\cdot\varphi^{-1}d\varphi\Big),
--   $$
--   and $u_\varphi=U_{R,h}$ with $R^*=O_\varphi$ and $h=-\int_0^\cdot\varphi'\varphi^{-1}$. The operator $V_R=\mathcal F^{-1}S^{-1}$ satisfies $V_RU^R_\varphi=E_\varphi V_R$, and $V_L=V_RJ$ satisfies $V_LU^L_\varphi=E_\varphi V_L$, for all $\varphi\in H(G)$.
--
--   This is the computation that proves the main theorem.
--
--   Differences from the source:
--   - encoding: G a compact connected Lie subgroup of GL_n(ℝ), 𝔤 its tangent space at e, with an Ad_G-invariant inner product → a subgroup with CompactSpace and ConnectedSpace, and a MatrixLieAlgebra structure (E, incl, Ad, bracket); reason: a compact subgroup of GL_n(ℝ) is a closed Lie subgroup, and the structure is determined by 𝔤 and the inner product
--   - encoding: p_t = e^{tΔ/2}δ_e, the fundamental solution of (2.1), for a bi-invariant Haar measure dx → hypotheses IsHeatKernel L m p (p jointly smooth on (0,∞)×G, (2.1) pointwise for t > 0, ∫p_t f dm → f(e) for continuous f) for a Haar measure m, and μ given by IsWienerMeasure m p T μ; reason: these conditions determine p_t for t > 0 (theorem_2_1); (2.2) does not depend on the normalization of m; a Haar measure on a compact group is bi-invariant
--   - encoding: H(G) through ‖h‖_{H,T} < ∞ with |h⁻¹h′| in 𝔤 → entrywise absolutely continuous paths whose g-valued h⁻¹h′ (read by the inverse of incl) is in L²; reason: h⁻¹h′ is in 𝔤 for a.e. t, and on G entrywise absolute continuity is absolute continuity
--   - encoding: the Wiener measure ν on W(𝔤), not spelled out → centred Gaussian with Cov(⟨a,w_s⟩,⟨b,w_t⟩) = ⟨a,b⟩ min(s,t); reason: the condition is basis-free and determines ν
--   - encoding: O_ϕ(w) = ∫₀^· Ad_ϕ δw_s → pathwise by parts: Ad_{ϕ_t}w_t − ∫₀ᵗ Ad_{ϕ_s}[ϕ⁻¹ϕ′(s),w_s]ds; reason: ϕ is absolutely continuous; this equals the stochastic integral ν-a.e. and is defined for every w
--   - encoding: the integral ∫₀ᵀ⟨a,dw_s⟩ → the L²(ν) limit along step functions, as a representative chosen by Classical.epsilon; reason: it is unique ν-a.e. by wiener_integral_isometry
--   - encoding: the Cameron-Martin space H(𝔤) of paths → L²([0,T];𝔤) through a ↦ ∫₀^·a; reason: this embedding is an isometry for the norm of H(𝔤)
--   - reading: R a topological homeomorphism of W* with adjoint R*: W → W → R orthogonal on H with a bounded bijection R* of W such that R*j = jR; reason: R* is defined on all of W only if the homeomorphism is weak-*; R*j = jR is the defining identity tested on j(H)
--   - encoding: F by Definition 17 of Driver-Hall, with a heuristic integral formula → the unitary with Fϕ̂ = e^{−|ϕ|²}e^{−⟨ϕ,·⟩}, the second identity of (5.2); reason: both families are total with Gram matrix exp(−½|ϕ−ψ|²), so this determines F
--   - encoding: ⟨h,w⟩ for h ∈ H → the L²(Γ) limit, as a representative chosen by Classical.epsilon (pairing); reason: unique a.e. by pairing_isometry
--   - encoding: Z^R_ϕ, Z^L_ϕ the densities of Theorem 2.14 → rnDeriv of the laws of g ↦ gϕ⁻¹ and g ↦ ϕg with respect to μ; reason: this is what ∫F(gϕ)Z^R dμ = ∫F dμ = ∫F(ϕ⁻¹g)Z^L dμ says; theorem_2_14 identifies them with the printed exponentials
--   - encoding: operators defined by formulas on L² → unitary operators asserted to exist with these a.e. formulas on H(G); reason: f∘R_ϕ of an a.e. class is meaningful by quasi-invariance, and the formula determines the operator
--   - encoding: B^L, B^R μ-a.e. defined maps → AEMeasurable maps W(G) → W(𝔤) that satisfy the limit predicates; reason: such a map is determined μ-a.e. by the predicates and path continuity
--   - correction: Definition 5.7: phase coefficient 1, exp(i∫⟨ϕ⁻¹ϕ′,dw⟩) → coefficient 1/2; reason: on G = SO(2), T = 1, with ϕ_n = exp(θ_n J) and θ_n′ orthonormal, ‖N⁻¹Σ E_{ϕ_n}ξ‖² → e⁻¹‖ξ‖² for every ξ, while ‖N⁻¹Σ U^R_{ϕ_n}1‖² → e^{−1/4}, so the printed E is not equivalent to U^R; Proposition 5.5 itself produces 1/2
--   - correction: Definition 5.7: integrand ϕ⁻¹ϕ′ → integrand ϕ′ϕ⁻¹; reason: on G = SO(3), ϕ = exp(tA), ψ = exp(tB) in different planes, the integrands of E_ϕE_ψ1 and E_{ϕψ}1 differ by (t²/2)([A,[A,B]]+[B,[A,B]]) + O(t³) ≠ 0, so the printed E is not a homomorphism, while (ϕψ)′(ϕψ)⁻¹ = ϕ′ϕ⁻¹ + Ad_ϕ(ψ′ψ⁻¹) is the cocycle
--   - correction: (5.1): e^{⟨h,w⟩−|h|²/2}f((R*)⁻¹(w−h)) → e^{⟨h,w⟩/2−|h|²/4}f((R*)⁻¹(w−h)); reason: with the printed factor and f = 1 the norm² is e^{|h|²} ≠ 1, so U is not unitary; the first two lines of (5.1) and the proof of Proposition 5.5 take the square root
--   - correction: (5.5): phase ½∫⟨ϕ⁻¹ϕ′,dw⟩ → −½∫⟨ϕ′ϕ⁻¹,dw⟩; reason: Theorem 2.14's density; on SO(2) with f = 1 the printed form has the wrong sign of I(ϕ′)
--   - correction: R*(w) = O_{ϕ⁻¹}w, h = −ϕ⁻¹dϕ, intertwiner F∘(B^L)* → R* = O_ϕ, h = −∫ϕ′ϕ⁻¹, V_R = F⁻¹∘((B^L)*)⁻¹, V_L = V_R∘J; reason: (5.1) applies (R*)⁻¹, so R* = O_{ϕ⁻¹} would give f(O_ϕ(w−h)), not the f(O_{ϕ⁻¹}w + ∫ϕ⁻¹dϕ) of (5.5); h must be the path −∫ϕ′ϕ⁻¹ for the exponent of (5.5) and O_{ϕ⁻¹}(∫ϕ′ϕ⁻¹) = ∫ϕ⁻¹ϕ′; (B^L)* maps L²(ν) to L²(μ), so the intertwiner from L²(μ) is its inverse, and F U_{R,h} F⁻¹ has phase −(i/2)I(ϕ′ϕ⁻¹), so F⁻¹ is the conjugation that gives E_ϕ
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, (5.4)-(5.5), pp.18-19 (corrected)

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_IsHeatKernel
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_IsWienerMeasure
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_primitive
import Definitions.Def_BrownianEnergyRep_rotation__ef917c
import Definitions.Def_BrownianEnergyRep_wienerIntegral
import Definitions.Def_BrownianEnergyRep_IsRightBrownianRep
import Definitions.Def_BrownianEnergyRep_IsLeftBrownianRep
import Definitions.Def_BrownianEnergyRep_IsEnergyRep
import Definitions.Def_BrownianEnergyRep_IsLeftItoMap
import Definitions.Def_BrownianEnergyRep_IsInversionOperator
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace
import Definitions.Def_BrownianEnergyRep_Rotation
import Definitions.Def_BrownianEnergyRep_IsFourierWiener
import Definitions.Def_BrownianEnergyRep_IsGaussianRegularRep
import Definitions.Def_BrownianEnergyRep_IsPathWienerSpace

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- (5.5) and the intertwiners (arXiv:1511.07378v1, proof of Theorem 5.8, pp.18-19), corrected: `(B^L)*` carries `U^R_ϕ` to
`u_ϕ`, `(u_ϕ f)(w) = exp(−½∫⟨ϕ′ϕ⁻¹,dw⟩ − ¼‖ϕ‖²_{H,T}) f(O_{ϕ⁻¹}w + ∫₀^·ϕ⁻¹dϕ)`, which is `U_{R,h}` with `R* = O_ϕ`,
`h = −∫₀^·ϕ′ϕ⁻¹`; then `F⁻¹((B^L)*)⁻¹` intertwines `U^R` with `E`, and its composite with `J` intertwines `U^L` with `E`. -/
theorem equation_5_5 {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [CompactSpace ↥G] [ConnectedSpace ↥G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : MatrixLieAlgebra G E) (T : ℝ) [Fact (0 < T)]
    (m : Measure ↥G) [m.IsHaarMeasure] (p : ℝ → ↥G → ℝ) (hp : IsHeatKernel L m p)
    (μ : Measure ↥(WienerGroup G T)) (hμ : IsWienerMeasure m p T μ)
    (A : AbstractWienerSpace (Lp E 2 (volume.restrict (Ioc (0 : ℝ) T))) ↥(WienerPath E T))
    (hA : IsPathWienerSpace A) (BL : ↥(WienerGroup G T) → ↥(WienerPath E T))
    (hBL : IsLeftItoMap L μ BL) (UR : ↥(WienerGroup G T) → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ))
    (hUR : IsRightBrownianRep L μ UR) :
    ∃ S : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
      (∀ f : Lp ℂ 2 A.Γ, (S f : ↥(WienerGroup G T) → ℂ) =ᵐ[μ] fun γ => f (BL γ)) ∧
      (∀ ϕ ∈ FiniteEnergy L T, ∃ (u : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 A.Γ) (ρ : Rotation A)
          (hk : MemLp (fun s => -rightLog L ϕ s) 2 (volume.restrict (Ioc 0 T))),
        (∀ f : Lp ℂ 2 A.Γ, UR ϕ (S f) = S (u f)) ∧
        (∀ f : Lp ℂ 2 A.Γ, (u f : ↥(WienerPath E T) → ℂ) =ᵐ[A.Γ]
          fun w => (Real.exp (-(1 / 2) * wienerIntegral A.Γ (rightLog L ϕ) w -
            (1 / 4) * energy L ϕ) : ℂ) *
              f (rotation L ϕ⁻¹ w + primitive T (leftLog L ϕ))) ∧
        (∀ w, ρ.adj w = rotation L ϕ w) ∧ IsGaussianRegularRep A ρ (hk.toLp _) u) ∧
      ∀ (F : Lp ℂ 2 A.Γ ≃ₗᵢ[ℂ] Lp ℂ 2 A.Γ), IsFourierWiener A F →
      ∀ (UL : ↥(WienerGroup G T) → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)), IsLeftBrownianRep L μ UL →
      ∀ J, IsInversionOperator μ J →
      ∀ En, IsEnergyRep L A.Γ En → ∀ ϕ ∈ FiniteEnergy L T, ∀ f : Lp ℂ 2 μ,
        F.symm (S.symm (UR ϕ f)) = En ϕ (F.symm (S.symm f)) ∧
        F.symm (S.symm (J (UL ϕ f))) = En ϕ (F.symm (S.symm (J f))) := by sorry

end BrownianEnergyRep
