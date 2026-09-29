-- Prove2me | Theorems.Thm_DeligneSerre_eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace
-- name    : DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/da4610e3-187d-55fc-8e4d-baffb9126bba
-- title:
--   Deligne–Serre: Euler factors and tame level exponents for weight one
-- statement:
--   Let $\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{GL}_2(\mathbb C)$ be a homomorphism satisfying [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17), i.e. there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho\sigma=1$ whenever $\sigma$ fixes $L$ pointwise, and assume $\det\rho(c)=-1$ for the automorphism $c$ of $\overline{\mathbb Q}$ obtained by restricting complex conjugation. Let $M\ge 1$, let $\varepsilon$ be a $\mathbb C$-valued Dirichlet character mod $M$, let $g,g'$ be weight one cusp forms on $\Gamma_1(M)$, and $c\neq0$ a complex number; write $b_n$, $b'_n$ for the $q$-expansion coefficients of $g$, $g'$. Assume $b_1=1$; $b_{pn}+\varepsilon(p)\,[p\mid n]\,b_{n/p}=b_pb_n$ for primes $p\nmid M$ and all $n$; $b_{\ell n}=b_\ell b_n$ for primes $\ell\mid M$ and all $n$; $g(\gamma\tau)=\varepsilon(d)(c_\gamma\tau+d)g(\tau)$ for $\gamma\in\Gamma_0(M)$ with lower row $(c_\gamma,d)$; $b'_n=\overline{b_n}$; $g(\tau')=c\,\tau\,g'(\tau)$ whenever $\tau'\cdot M\tau=-1$; and $\|b_\ell\|\le1$ for primes $\ell\mid M$. Assume finally there is $N_0\neq0$ such that for every prime $p\nmid N_0$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ in its nonunits, and every $\sigma$ in the decomposition group acting as $x\mapsto x^p$ on the residue field of $A$, one has $b_p=\operatorname{tr}\rho(\sigma)$ and $\varepsilon(p)=\det\rho(\sigma)$. The conclusion has three parts, in which $I_A$ denotes the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ and $V^{I_A}\subseteq\mathbb C^2$ the subspace of vectors fixed by the restriction of the representation $\mathbb C^2$ attached to $\rho$ to $I_A$. First, for every prime $p\nmid M$ and every $A$ over $p$: $\rho$ is trivial on $I_A$, and $b_p=\operatorname{tr}\rho(\sigma)$, $\varepsilon(p)=\det\rho(\sigma)$ for every Frobenius $\sigma$ at $A$. Secondly, for every prime $\ell$ and every $A$ over $\ell$ with $\#\rho(I_A)$ coprime to $\ell$: the exponent of $\ell$ in $M$ plus $\dim_{\mathbb C}V^{I_A}$ equals $2$, and every Frobenius $\sigma$ at $A$ preserves $V^{I_A}$ with $b_\ell$ the trace of the induced endomorphism. Thirdly, for every prime $\ell\mid M$ and every $A$ over $\ell$: $\dim_{\mathbb C}V^{I_A}<2$, and again every Frobenius $\sigma$ at $A$ preserves $V^{I_A}$ and $b_\ell$ is the trace of its restriction.
--
--   This is the form taken here by Théorème 4.6 and Corollaire 4.7 of Deligne–Serre, stated for a given odd Artin representation of dimension two that is only assumed to match the coefficients of the weight one form away from the primes dividing some fixed $N_0$: the matching then extends to all primes not dividing $M$, $\rho$ is unramified there, and at tamely ramified primes the exponent of $\ell$ in $M$ is the codimension of the inertia invariants, with $b_\ell$ the Frobenius trace on those invariants. It is used by [`DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`](thm.html#DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace.lean

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

theorem DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace
    (ρ : Γℚ →* GL (Fin 2) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (hodd : ((ρ complexConjugation : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = -1)
    (M : ℕ) [NeZero M] (ε : DirichletCharacter ℂ M) (g g' : CuspForm (Gamma1 M) 1) (c : ℂ)
    (hg₁ : ModularFormClass.qCoeff g 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          ModularFormClass.qCoeff g p * ModularFormClass.qCoeff g n)
    (hU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) =
          ModularFormClass.qCoeff g ℓ * ModularFormClass.qCoeff g n)
    (hε : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
        g (γ • τ) =
          ε ((γ 1 1 : ℤ) : ZMod M) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * g τ))
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n))
    (hc : c ≠ 0)
    (hW : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = c * (τ : ℂ) * g' τ)
    (hLi : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ‖ModularFormClass.qCoeff g ℓ‖ ≤ 1)
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0)
    (hρg : ∀ p : ℕ, p.Prime → ¬ p ∣ N₀ →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ModularFormClass.qCoeff g p =
                ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
            ε (p : ZMod M) = ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det) :
    (∀ p : ℕ, p.Prime → ¬ p ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ModularFormClass.qCoeff g p =
              ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
          ε (p : ZMod M) = ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det) ∧
    (∀ ℓ : ℕ, ℓ.Prime →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime ℓ →
          M.factorization ℓ +
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
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        Module.finrank ℂ (Representation.invariants
            ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype)) < 2 ∧
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
          ∃ hσ : ∀ v ∈ Representation.invariants
                ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
              Deformation.matrixRepresentation ρ σ v ∈ Representation.invariants
                ((Deformation.matrixRepresentation ρ).comp (A.inertiaSubgroupIn ℚ).subtype),
            ModularFormClass.qCoeff g ℓ =
              LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρ σ).restrict hσ)) := by sorry
