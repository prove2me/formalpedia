-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_inertia_eq_one_and_isRoot_charpoly_of_eigenpacketOccursAt_div
-- name    : CuspForm.IsEigenformWith.inertia_eq_one_and_isRoot_charpoly_of_eigenpacketOccursAt_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/3d00ee9e-a3ea-5832-8989-f9651c1ee9d6
-- title:
--   Unramified at q with a_q a Frobenius eigenvalue
-- statement:
--   Fix $M \ge 1$, a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$, and $h \in S_2(\Gamma_1(M))$ satisfying [`CuspForm.IsEigenformWith`](def/CuspForm_PrimitiveFormGamma1.html#L19): the first $q$-expansion coefficient of $h$ is $1$, for each prime $p \nmid M$ and each $n$ one has $a_{pn}(h) + \varepsilon(p)\,p^{k-1}\,a_{n/p}(h) = a_p(h)a_n(h)$ (the second term read as $0$ unless $p \mid n$) with $k = 2$, for each prime $\ell \mid M$ one has $a_{\ell n}(h) = a_\ell(h)a_n(h)$, and $h$ transforms under $\Gamma_0(M)$ with nebentypus $\varepsilon$. Let $\lambda$ be a prime, $S$ a finite set of naturals, and $O'$ a complete discrete valuation ring of characteristic zero with finite residue field in whose maximal ideal $\lambda$ lies. Let $R$ be a commutative ring with an injective ring homomorphism $\mathrm{toC} : R \to \mathbb{C}$ and a ring homomorphism $\varphi : R \to O'$, and let $b, e : \mathbb{N} \to R$ satisfy $\mathrm{toC}(b_\ell) = a_\ell(h)$ and $\mathrm{toC}(e_\ell) = \varepsilon(\ell)$ for all primes $\ell \nmid M$ with $\ell \notin S$. Let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $O'$, i.e. a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ to the endomorphisms of a free finite $O'$-module $V$ of rank $2$, continuous for the maximal-adic topology, such that for every prime $\ell \nmid M$ with $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition group of $A$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, the characteristic polynomial of $\rho(\sigma)$ is $X^2 - \varphi(b_\ell) X + \varphi(e_\ell)\ell$. Finally let $q$ be a prime with $q \ne \lambda$, $q \mid M$, $q^2 \nmid M$, with $\mathrm{toC}(b_q) = a_q(h)$, and assume the eigenpacket $(a_n(h), \varepsilon(n))$ in weight $2$ already occurs at level $M/q$, i.e. there are a character $\varepsilon'$ modulo $M/q$, a nonzero $h' \in S_2(\Gamma_1(M/q))$ with nebentypus $\varepsilon'$ and a finite set of primes outside which $\varepsilon'(p) = \varepsilon(p)$ and $h'$ satisfies the weight-two Hecke relation with eigenvalue $a_p(h)$. The conclusion: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ having $q$ as a non-unit, $\rho(\sigma) = 1$ for every $\sigma$ in the image of the inertia subgroup of $P$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and for every $\tau$ in the decomposition group of $P$ acting as $x \mapsto x^q$ on the residue field of $P$, the element $\varphi(b_q)$ is a root of the characteristic polynomial of $\rho(\tau)$.
--
--   This is the "old at $q$" case of the local description, at a prime exactly dividing the level, of the $\lambda$-adic representation attached to a weight-two eigenform of level $M$ and nebentypus $\varepsilon$: the representation is unramified at $q$ and the $U_q$-eigenvalue appears as an eigenvalue of Frobenius. It is stated for an arbitrary two-dimensional lattice carrying the Frobenius data of $h$ away from $MS$, and feeds the construction of a basis in which inertia at a prime dividing the level acts by scalars for residually absolutely irreducible representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_inertia_eq_one_and_isRoot_charpoly_of_eigenpacketOccursAt_div.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsEigenformWith.inertia_eq_one_and_isRoot_charpoly_of_eigenpacketOccursAt_div
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
    (q : ℕ) (hq : q.Prime) (hqlam : q ≠ lam) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hbq : toC (b q) = ModularFormClass.qCoeff h q)
    (hold : CuspForm.EigenpacketOccursAt 2 (fun n => ModularFormClass.qCoeff h n)
      (fun n => ε (n : ZMod M)) (M / q)) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1) ∧
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ q →
        (LinearMap.charpoly (ρ.ρ τ)).IsRoot (φ (b q)) := by sorry
