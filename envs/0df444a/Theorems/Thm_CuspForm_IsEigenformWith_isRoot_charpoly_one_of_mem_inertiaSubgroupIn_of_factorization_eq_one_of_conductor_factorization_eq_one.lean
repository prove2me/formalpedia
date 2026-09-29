-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_isRoot_charpoly_one_of_mem_inertiaSubgroupIn_of_factorization_eq_one_of_conductor_factorization_eq_one
-- name    : CuspForm.IsEigenformWith.isRoot_charpoly_one_of_mem_inertiaSubgroupIn_of_factorization_eq_one_of_conductor_factorization_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/cc30b5e2-943e-5463-8dd4-4d2738938f3b
-- title:
--   Inertia eigenvalue 1 at q when v_q(M)=v_q(condε)=1
-- statement:
--   Let $M\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $h$ be a weight-two cusp form on $\Gamma_1(M)$ which is an eigenform with nebentypus $\varepsilon$ in the sense of the project predicate: its first $q$-expansion coefficient is $1$, for every prime $p\nmid M$ and every $n$ one has $a_{pn}(h)+\varepsilon(p)\,p\,[p\mid n]\,a_{n/p}(h)=a_p(h)a_n(h)$, for every prime $\ell\mid M$ and every $n$ one has $a_{\ell n}(h)=a_\ell(h)a_n(h)$, and $h(\gamma\tau)=\varepsilon(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^2h(\tau)$ for all $\gamma\in\Gamma_0(M)$. Let $\lambda$ be a prime, $S$ a finite set of naturals, and $O'$ a characteristic-zero complete discrete valuation domain with finite residue field whose maximal ideal contains $\lambda$. Let $R$ be a commutative ring with an injective ring homomorphism $\mathrm{toC}\colon R\to\mathbb{C}$ and a ring homomorphism $\varphi\colon R\to O'$, and let $b,e\colon\mathbb{N}\to R$ satisfy $\mathrm{toC}(b_\ell)=a_\ell(h)$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for every prime $\ell\nmid M$ with $\ell\notin S$. Let $\rho$ be an adic Galois representation over $O'$, i.e. a free $O'$-module $V$ of rank two, finite over $O'$, together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\operatorname{End}_{O'}(V)$ that is continuous for the maximal-adic filtration (for each $n$ there is a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ whose pointwise stabiliser acts trivially modulo $\mathfrak{m}^n V$), and assume that for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting on the residue field of $A$ by $x\mapsto x^{\ell}$, the characteristic polynomial of $\rho(\sigma)$ is $X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$. Let $q$ be a prime with $q\neq\lambda$ such that $q$ divides $M$ exactly once and divides the conductor of $\varepsilon$ exactly once. Then for every valuation subring $P$ of $\overline{\mathbb{Q}}$ having $q$ as a non-unit and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$, the characteristic polynomial of $\rho(\sigma)$ has $1$ as a root.
--
--   This is the local information at $q$ supplied by the local Langlands correspondence for $\mathrm{GL}_2$ and its compatibility with $\lambda$-adic representations, in the case where $q$ divides the level and the conductor of the nebentypus exactly once: inertia at $q$ acts with eigenvalue $1$, so an inertia-invariant vector exists. It is stated for an arbitrary eigenform (not necessarily a newform) and for any representation with the prescribed Frobenius characteristic polynomials away from $M$ and $S$, and it feeds the construction of representations with inertia acting trivially at such $q$ used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_isRoot_charpoly_one_of_mem_inertiaSubgroupIn_of_factorization_eq_one_of_conductor_factorization_eq_one.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsEigenformWith.isRoot_charpoly_one_of_mem_inertiaSubgroupIn_of_factorization_eq_one_of_conductor_factorization_eq_one
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (φ (b ℓ)) * X + C (φ (e ℓ) * (ℓ : O')))
    (q : ℕ) [Fact q.Prime] (hqlam : q ≠ lam)
    (hMq : M.factorization q = 1) (hεq : ε.conductor.factorization q = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (LinearMap.charpoly (ρ.ρ σ)).IsRoot 1 := by sorry
