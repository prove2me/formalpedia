-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_exists_ne_zero_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one
-- name    : CuspForm.IsPrimitiveForm.exists_ne_zero_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/12dd4682-c8a9-50b1-a2da-e4a9a9db8144
-- title:
--   Nonzero inertia invariants at q when v_q(M)=1
-- statement:
--   Fix $M\ge 1$, a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb C$, and a cusp form $h$ of weight $2$ on $\Gamma_1(M)$ which is primitive for $\varepsilon$, i.e. $h$ has normalised $q$-expansion ($a_1=1$), satisfies the Hecke recursions at primes $p\nmid M$, is multiplicative at primes dividing $M$, has nebentypus $\varepsilon$, and its eigenpacket $(a_n(h),\varepsilon)$ occurs at no proper divisor $M'\mid M$. Let $\lambda$ be prime, $S$ a finite set of naturals, and $O'$ a characteristic-zero discrete valuation domain, complete for its maximal ideal and with finite residue field, with $\lambda$ in the maximal ideal. Let $R$ be a commutative ring with an injective ring map $\mathrm{toC}:R\to\mathbb C$ and a ring map $\varphi:R\to O'$, and $b,e:\mathbb N\to R$ with $\mathrm{toC}(b_\ell)=a_\ell(h)$, $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for all primes $\ell\nmid M$, $\ell\notin S$. Let $\rho$ be an adically continuous representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on a free $O'$-module $V$ of rank $2$ such that for every prime $\ell\nmid M$, $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit, and every $\sigma$ which is Frobenius at $A$ (lying in the decomposition group and acting as $x\mapsto x^{\ell}$ on the residue field), $\mathrm{charpoly}(\rho(\sigma))=X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$. Let $q\ne\lambda$ be prime with $v_q(M)=1$, let $\Phi$ be an adelic lift of $h$ to $\mathrm{GL}_2$ of the adeles of $\mathbb Q$ (left invariant under the global points, right invariant under the level-one subgroup at the finite places for the ideal $(M)$, and given at matrices with trivial finite part and totally positive archimedean part by the weight-$2$ slash action of $h$ evaluated at $i$), let $\nu_1,\nu_2:\mathbb Q_q^\times\to\mathbb C^\times$ with $\nu_1$ trivial on units of norm $1$, and let $f$ be a nonzero $\mathbb C$-linear, $\mathrm{GL}_2(\mathbb Q_q)$-equivariant map from the adelic span of $\Phi$ to the principal series carrier of $(\nu_1,\nu_2)$. Then for every valuation subring $P$ of $\overline{\mathbb Q}$ in which $q$ is a nonunit there is a nonzero $v\in V$ fixed by $\rho(\sigma)$ for all $\sigma$ in the inertia subgroup of $P$ over $\mathbb Q$.
--
--   This is the principal-series case, at $q$-exponent exactly one in the level, of the local–global statement that the $\lambda$-adic representation attached to a weight-two primitive form has nonzero inertia invariants at a prime $q\ne\lambda$ whose local component is a principal series with unramified first character; classically it rests on the Deligne–Rapoport description of the reduction of the modular curve. It feeds the analysis of inertia at primes with $v_q(M)=2$ for newforms, where the characteristic polynomial on inertia is identified with the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_exists_ne_zero_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one.lean

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

theorem CuspForm.IsPrimitiveForm.exists_ne_zero_forall_inertiaSubgroupIn_apply_eq_self_of_linearMap_psCarrier_isUnramified_of_factorization_eq_one
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
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
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hν₁ : LocalNewvector.IsUnramified q ν₁)
    (hM1 : M.factorization q = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∃ v : ρ.V, v ≠ 0 ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ v = v := by sorry
