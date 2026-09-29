-- Prove2me | Theorems.Thm_DeligneSerre_exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace
-- name    : DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/5427f82d-aa0e-54fe-a1d6-1fb5f49fb1c4
-- title:
--   Deligne–Serre: weight-one form with tame level exponents
-- statement:
--   Let $\rho\colon \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{GL}_2(\mathbb C)$ be a homomorphism which factors through a finite level (there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ with $[L:\mathbb Q]<\infty$ such that $\rho(\sigma)=1$ whenever $\sigma$ fixes $L$ pointwise), suppose the associated representation of $\rho$ on $\mathbb C^2$ satisfies `IsIrreducible`, and suppose $\det\rho(c)=-1$ for $c$ the restriction to $\overline{\mathbb Q}$ of complex conjugation on $\mathbb C$. Let $N\neq 0$ and let $f$ be a weight-one cusp form on $\Gamma_1(N)$ with $q$-expansion coefficients $a_n=$ `qCoeff f n`, normalised by $a_1=1$, such that for every prime $p\nmid N$, every valuation subring $A\subseteq\overline{\mathbb Q}$ with $p$ in the non-units of $A$ and every $\sigma$ in the decomposition group of $A$ over $\mathbb Q$ acting as $x\mapsto x^p$ on the residue field of $A$ one has $a_p=\operatorname{tr}\rho(\sigma)$ and $a_{pn}+\det\rho(\sigma)\,[p\mid n]\,a_{n/p}=a_pa_n$ for all $n$, and such that $a_{\ell n}=a_\ell a_n$ for all $n$ when $\ell\mid N$ is prime. Then there are $N'\neq 0$ and a weight-one cusp form $g$ on $\Gamma_1(N')$, with coefficients $b_n$, such that: $b_1=1$; the same two Frobenius relations hold for all primes $p\nmid N'$, all such $A$ above $p$ and all such $\sigma$; $b_{\ell n}=b_\ell b_n$ for all $n$ and all primes $\ell\mid N'$; for every prime $\ell$ and every such $A$ above $\ell$ for which the cardinality of the image under $\rho$ of the inertia subgroup $I_A\le \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ is coprime to $\ell$, the exponent of $\ell$ in $N'$ plus $\dim_{\mathbb C}(\mathbb C^2)^{I_A}$ equals $2$, and for every Frobenius $\sigma$ at $\ell$ the operator $\rho(\sigma)$ preserves $(\mathbb C^2)^{I_A}$ and $b_\ell$ is the trace of its restriction there; and finally, for $\gamma\in\Gamma_0(N')$, a prime $p\nmid N'$ with $\gamma_{1,1}\equiv p \pmod{N'}$, $A$ above $p$ and $\sigma$ Frobenius at $p$, one has $g(\gamma\tau)=\det\rho(\sigma)\,(\gamma_{1,0}\tau+\gamma_{1,1})\,g(\tau)$ for all $\tau$ in the upper half-plane.
--
--   This is the consumer form of Deligne–Serre's theorem on weight-one forms: an odd complex Artin representation matched by a normalised weight-one eigenform away from a level can be matched by a form whose level exponents at tamely ramified primes are the codimensions of the inertia invariants, whose coefficient at such a prime is the trace of Frobenius on the invariants, and whose nebentypus is $\det\rho$. It is invoked in the Langlands–Tunnell step, to produce weight-one forms of controlled level and nebentypus from the representations constructed there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace
    (ρ : Γℚ →* GL (Fin 2) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (hirr : (Deformation.matrixRepresentation ρ).IsIrreducible)
    (hodd : ((ρ complexConjugation : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = -1)
    (N : ℕ) [NeZero N] (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ModularFormClass.qCoeff f p =
                ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
            ∀ n : ℕ, ModularFormClass.qCoeff f (p * n) +
                ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det *
                  (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
              ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (hfU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (ℓ * n) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff f n) :
    ∃ (N' : ℕ) (_ : NeZero N') (g : CuspForm (Gamma1 N') 1),
      ModularFormClass.qCoeff g 1 = 1 ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N' →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ModularFormClass.qCoeff g p =
                ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
            ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
                ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det *
                  (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
              ModularFormClass.qCoeff g p * ModularFormClass.qCoeff g n) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N' → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) =
          ModularFormClass.qCoeff g ℓ * ModularFormClass.qCoeff g n) ∧
      (∀ ℓ : ℕ, ℓ.Prime →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime ℓ →
            N'.factorization ℓ +
                Module.finrank ℂ (Representation.invariants
                  ((Deformation.matrixRepresentation ρ).comp
                    (A.inertiaSubgroupIn ℚ).subtype)) = 2 ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
              ∃ hσ : ∀ v ∈ Representation.invariants
                    ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
                  Deformation.matrixRepresentation ρ σ v ∈ Representation.invariants
                    ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
                ModularFormClass.qCoeff g ℓ =
                  LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρ σ).restrict hσ)) ∧
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 N' →
        ∀ p : ℕ, p.Prime → ¬ p ∣ N' → ((γ 1 1 : ℤ) : ZMod N') = (p : ZMod N') →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
              ∀ τ : UpperHalfPlane,
                g (γ • τ) =
                  ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det *
                    ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * g τ)) := by sorry
