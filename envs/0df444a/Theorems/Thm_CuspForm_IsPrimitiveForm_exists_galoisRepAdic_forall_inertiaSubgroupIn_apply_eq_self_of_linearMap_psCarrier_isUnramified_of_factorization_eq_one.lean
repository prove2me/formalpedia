-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one
-- name    : CuspForm.IsPrimitiveForm.exists_galoisRepAdic_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/89dcf4d5-9916-5b13-b143-a1dce00c6927
-- title:
--   Inertia invariants at q for v_q(M)=1, unramified principal series
-- statement:
--   Let $M\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$ and let $h$ be a cusp form of weight $2$ on $\Gamma_1(M)$ which is primitive with nebentypus $\varepsilon$, i.e. $h$ is a normalised Hecke eigenform ($q$-coefficient $1$ at $n=1$, the Hecke relations at primes $p\nmid M$ involving $\varepsilon(p)p^{k-1}$, multiplicativity at primes dividing $M$, and nebentypus $\varepsilon$) whose eigenpacket of coefficients and character values occurs at no proper divisor of $M$. Let $\lambda$ be a prime, $S$ a finite set of naturals with $\lambda\in S$, and $\mathcal{O}'$ a characteristic-zero discrete valuation domain, adically complete for its maximal ideal, with finite residue field and with $\lambda$ in that maximal ideal. Let $R$ be a commutative ring, $\mathrm{toC}:R\to\mathbb{C}$ an injective ring homomorphism, $\varphi:R\to\mathcal{O}'$ a ring homomorphism, and $b,e:\mathbb{N}\to R$ with $\mathrm{toC}(b_\ell)=a_\ell(h)$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for every prime $\ell\nmid M$ with $\ell\notin S$. Let $q$ be a prime, $q\ne\lambda$, let $\Phi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be an adelic lift of $h$ (left invariant under the global points $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the finite level-one subgroup attached to the ideal $(M)$, and equal to the weight-$2$ slash action of $h$ evaluated at $i$ on elements with trivial finite part and archimedean component of positive determinant), let $\nu_1,\nu_2:\mathbb{Q}_q^\times\to\mathbb{C}^\times$ be characters with $\nu_1$ unramified (trivial on units of norm $1$), and let $f$ be a nonzero $\mathbb{C}$-linear map from the span of the adelic translates of $\Phi$ to the principal series carrier $B(\nu_1,\nu_2)$ at $q$ which is $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant. Assume $v_q(M)=1$. Then there is a characteristic-zero discrete valuation domain $\mathcal{O}''$, adically complete with finite residue field, which is a module-finite $\mathcal{O}'$-algebra whose structure map is local and injective, together with a two-dimensional adically continuous Galois representation $\rho$ over $\mathcal{O}''$ (a free $\mathcal{O}''$-module $V$ of rank $2$ with a homomorphism from the automorphism group of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ to $\mathrm{End}_{\mathcal{O}''}(V)$) such that, first, for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$ and every $\sigma$ which is a Frobenius at $\ell$ for $A$ (lying in the decomposition subgroup and acting as $x\mapsto x^{\ell}$ on the residue field of $A$), the characteristic polynomial of $\rho(\sigma)$ is $X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$ pushed forward to $\mathcal{O}''$; and second, for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$ there is a nonzero $v\in V$ fixed by $\rho(\sigma)$ for every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$.
--
--   This is the case $v_q(M)=1$ of the construction of a $\lambda$-adic realisation of a weight-two newform whose restriction to inertia at an auxiliary prime $q\ne\lambda$ has non-zero invariants, the input needed when the local component of $h$ at $q$ is a principal series $B(\nu_1,\nu_2)$ with $\nu_1$ unramified. It feeds the level-structure analysis at $q$ used in level lowering, and is cited by the companion statement that extracts the inertia-invariant vector alone.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one.lean

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsPrimitiveForm.exists_galoisRepAdic_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (q : ℕ) [Fact q.Prime] (hqlam : q ≠ lam)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hν₁ : LocalNewvector.IsUnramified q ν₁)
    (hM1 : M.factorization q = 1) :
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
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∃ v : ρ.V, v ≠ 0 ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ v = v := by sorry
