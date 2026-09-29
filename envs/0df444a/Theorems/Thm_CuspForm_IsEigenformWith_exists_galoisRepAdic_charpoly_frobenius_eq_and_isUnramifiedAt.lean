-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt
-- name    : CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/21929324-8b02-5e1e-8e25-5ecc810a38db
-- title:
--   λ-adic representation attached to a weight-two eigenform
-- statement:
--   Let $M\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb C$, and let $h$ be a cusp form of weight $2$ for $\Gamma_1(M)$ which is an eigenform with nebentypus $\varepsilon$ in the coefficient sense: writing $a_n$ for the $n$-th coefficient of the $q$-expansion of $h$ at the cusp (width $1$), one has $a_1=1$, the relations $a_{pn}+\varepsilon(p)\,p\,[p\mid n]\,a_{n/p}=a_p a_n$ for all primes $p\nmid M$ and all $n$, the relations $a_{\ell n}=a_\ell a_n$ for all primes $\ell\mid M$ and all $n$, and $h(\gamma\tau)=\varepsilon(d)\,(c\tau+d)^2 h(\tau)$ for all $\gamma=\begin{pmatrix}a&b\\ c&d\end{pmatrix}\in\Gamma_0(M)$ and all $\tau$ in the upper half-plane. Let $\lambda$ be a prime, let $S$ be a finite set of naturals with $\lambda\in S$, and let $\mathcal O'$ be a characteristic-zero discrete valuation domain, complete for the adic topology of its maximal ideal, with finite residue field, such that $\lambda$ lies in the maximal ideal. Let $R$ be a commutative ring equipped with an injective ring homomorphism $\mathrm{toC}:R\to\mathbb C$ and a ring homomorphism $\varphi:R\to\mathcal O'$, and let $b,e:\mathbb N\to R$ satisfy $\mathrm{toC}(b_\ell)=a_\ell$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell\bmod M)$ for every prime $\ell\nmid M$ with $\ell\notin S$. Then there exists a ring $\mathcal O''$ with the same properties (characteristic-zero complete discrete valuation domain with finite residue field), an $\mathcal O'$-algebra structure on $\mathcal O''$ making it module-finite over $\mathcal O'$ with local and injective structure map, together with $\rho$ a $\lambda$-adic Galois representation over $\mathcal O''$, that is: a free $\mathcal O''$-module $V$ of rank $2$ and a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ (the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_{\mathcal O''}(V)$ which is adically continuous, in the sense that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v-v\in\mathfrak m^n V$ for all $v\in V$ and all $\sigma$ fixing $L$ pointwise, such that: (i) for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ which is a Frobenius at $\ell$ for $A$ (that is, $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb Q$ and acts on the residue field of $A$ by $x\mapsto x^{\ell}$), the characteristic polynomial of $\rho(\sigma)$ is $X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$, images taken in $\mathcal O''$; and (ii) for every prime $\ell\nmid M$ with $\ell\ne\lambda$, $\rho$ is unramified at $\ell$, i.e. $\rho(\sigma)=1$ for every valuation subring $P$ of $\overline{\mathbb Q}$ having $\ell$ as a non-unit and every $\sigma$ in the image of the inertia subgroup of $P$ over $\mathbb Q$. Note that the Frobenius characteristic polynomial is asserted only for primes outside the auxiliary finite set $S$, while unramifiedness is asserted at all primes $\ell\nmid M$ with $\ell\neq\lambda$.
--
--   This is the Eichler–Shimura construction, in weight two, of the $\lambda$-adic Galois representation attached to a normalised Hecke eigenform on $\Gamma_1(M)$ with nebentypus, realised through the Tate module of the Jacobian of $X_1(M)$ with its commuting Hecke and diamond actions; the coefficient ring is allowed to grow to a module-finite extension $\mathcal O''$ of $\mathcal O'$. It is the source of the modular Galois representations used downstream, e.g. in the analysis of inertia and of residual Hecke characters in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
        (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
        (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O'')),
      Function.Injective (algebraMap O' O'') ∧
      ∃ ρ : GaloisRepAdic O'',
        (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap O' O'' (φ (b ℓ))) * X
                  + C (algebraMap O' O'' (φ (e ℓ) * (ℓ : O')))) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ρ.IsUnramifiedAt ℓ) := by sorry
