-- Prove2me | Theorems.Thm_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
-- name    : DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/c47f588e-b3ba-52e9-945c-de6e46618360
-- title:
--   Deligne–Serre gluing: mod-ℓ family yields complex representation
-- statement:
--   Fix a natural number $N$, a $\mathbb{Z}$-subalgebra $R \subseteq \mathbb{C}$ that is finite as a $\mathbb{Z}$-module, a natural number $m > 0$ and a primitive $m$-th root of unity $\zeta \in \mathbb{C}$ lying in $R$, together with two functions $t, d : \mathbb{N} \to \mathbb{C}$ whose values $t(p)$ and $d(p)$ lie in $R$ for every prime $p \nmid N$. Write $\Gamma_{\mathbb{Q}}$ for the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$. Assume that for every prime $\ell$ and every ring homomorphism $\varphi : R \to \mathbb{Z}/\ell$ there is a homomorphism $\rho : \Gamma_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{Z}/\ell)$ such that: (i) $\rho$ factors through a finite level, i.e. there is an intermediate field $L$ of $\mathbb{Q} \subseteq \mathrm{AlgebraicClosure}\ \mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $\rho\sigma = 1$ for every $\sigma$ fixing $L$ pointwise; (ii) the cardinality of the image of $\rho$ divides $m$; and (iii) for every prime $p \nmid N$ with $p \neq \ell$ and every valuation subring $A$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ in which $p$ is a non-unit, $\rho$ kills the image in $\Gamma_{\mathbb{Q}}$ of the inertia subgroup of $A$ over $\mathbb{Q}$, and every $\sigma$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^{p}$ has $\mathrm{charpoly}(\rho\sigma) = X^2 - \varphi(t(p))X + \varphi(d(p))$. The conclusion is that there exists a homomorphism $\rho : \Gamma_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{C})$ factoring through a finite level in the same sense, such that for every prime $p \nmid N$ (no exceptional prime is excluded now) and every valuation subring $A$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ in which $p$ is a non-unit, $\rho$ kills the image of the inertia subgroup of $A$, and every $\sigma$ in the decomposition subgroup of $A$ acting on the residue field by $x \mapsto x^{p}$ satisfies $\mathrm{tr}\,\rho\sigma = t(p)$ and $\det \rho\sigma = d(p)$.
--
--   This is the gluing step of §8.5–8.6 of Deligne–Serre's construction of the Galois representation attached to a weight one form: a compatible family of mod-$\ell$ two-dimensional representations with images of order dividing a fixed $m$, indexed by the degree-one reductions of an order $R$, is assembled into a single complex representation with finite image whose Frobenius traces and determinants are the prescribed values $t(p)$, $d(p)$. It is used by [`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`](thm.html#DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen), where $t(p)$ is the Hecke eigenvalue $a_p$ and $d(p)$ the nebentypus value $\varepsilon(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual
    (N : ℕ) (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R]
    (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (hζR : ζ ∈ R)
    (t d : ℕ → ℂ) (ht : ∀ p : ℕ, p.Prime → ¬ p ∣ N → t p ∈ R)
    (hd : ∀ p : ℕ, p.Prime → ¬ p ∣ N → d p ∈ R)
    (hfam : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (φ : R →+* ZMod ℓ),
      ∃ ρ : Γℚ →* GL (Fin 2) (ZMod ℓ), GaloisFactorsThroughFiniteLevel ρ ∧
        Nat.card (MonoidHom.range ρ) ∣ m ∧
        ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), p ≠ ℓ →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
                X ^ 2 - C (φ ⟨t p, ht p hp hpN⟩) * X + C (φ ⟨d p, hd p hp hpN⟩)) :
    ∃ ρ : Γℚ →* GL (Fin 2) ℂ, GaloisFactorsThroughFiniteLevel ρ ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = t p ∧
            ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = d p := by sorry
