-- Prove2me | Theorems.Thm_CuspForm_IsNewform_exists_charpoly_inertia_eq_and_pow_sub_one_ne_one_of_forall_linearMap_psCarrier_eq_zero_of_factorization_eq_two_of_irreducible_odd_of_ne_two
-- name    : CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_sub_one_ne_one_of_forall_linearMap_psCarrier_eq_zero_of_factorization_eq_two_of_irreducible_odd_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/d932af8a-0218-51a9-9ee6-fa7a142fe6f9
-- title:
--   Inertia at q is split with a^{q-1}≠ 1
-- statement:
--   Let $M$ be a non-zero natural number and let $g$ be a weight-two cusp form for $\Gamma_0(M)$ which is a newform, i.e. a normalized Hecke eigenform (the $q$-expansion coefficients satisfy $a_1=1$, multiplicativity at coprime arguments and the recursions $a_{p^{r+2}}=a_pa_{p^{r+1}}-p\,a_{p^r}$ for $p\nmid M$ and $a_{p^{r+2}}=a_pa_{p^{r+1}}$ for $p\mid M$) such that for no proper divisor $M'$ of $M$ does some normalized eigenform of level $M'$ agree with $g$ in all coefficients at primes not dividing $M$. Let $\lambda$ be a prime, $S$ a finite set of naturals, and $O'$ a complete discrete valuation ring which is a domain of characteristic zero with finite residue field, with $\lambda$ in its maximal ideal and $\lambda\neq 2$. Let $\chi_g$ be a ring homomorphism to $\mathbb{C}$ from the $\mathbb{Z}$-algebra generated inside $\operatorname{End}_{\mathbb{C}}$ of weight-two level-$M$ cusp forms by the operators $T_\ell$ ($\ell$ prime, $\ell\nmid M$, $\ell\notin S$) and $U_p$ ($p$ prime, $p\mid M$, $p\notin S$), sending each $T_\ell$ to the $\ell$-th $q$-expansion coefficient of $g$, and let $\iota$ be a ring homomorphism from the image of $\chi_g$ to $O'$. Let $\rho$ be a Galois representation over $O'$: a free $O'$-module $V$ of rank two, finite over $O'$, with a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\operatorname{End}_{O'}V$ which is adically continuous (for each $n$ some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ has the property that elements fixing it move every vector only inside $\mathfrak{m}^n V$), whose residual representation on the residue-field base change is irreducible (no proper non-zero invariant subspace) and odd (every involution $\neq 1$ has determinant $-1$), and such that for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$ and every $\sigma$ in the decomposition group of $A$ acting as $x\mapsto x^\ell$ on the residue field, the characteristic polynomial of $\rho(\sigma)$ is $X^2-\iota(\chi_g(T_\ell))X+\ell$. Let $q$ be a prime with $q\neq\lambda$ and $q$-adic valuation of $M$ exactly $2$, let $\Phi$ be a non-zero complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$ (left invariant under the global points, right invariant under the finite level-one subgroup at level $M$, and at elements with trivial finite part given by the weight-two slash of $g$ at $i$ along the archimedean component), and assume that for all characters $\mu_1,\mu_2$ of $\mathbb{Q}_q^\times$ every $\mathbb{C}$-linear $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant map from the span of the adelic translates of $\Phi$ to the principal series space of locally constant functions on $\mathrm{GL}_2(\mathbb{Q}_q)$ with the $(\mu_1,\mu_2)$-Borel transformation law vanishes. Then there exist a local domain $O''$, an injective local ring homomorphism $j:O'\to O''$ and a function $a$ from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $O''^\times$ such that for every valuation subring $P$ of $\overline{\mathbb{Q}}$ having $q$ as a non-unit and every $\sigma$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $P$ one has $(\operatorname{charpoly}\rho(\sigma))^{j}=(X-a(\sigma))(X-a(\sigma)^{-1})$, and for every such $P$ some $\sigma$ in that inertia subgroup satisfies $a(\sigma)^{q-1}\neq 1$.
--
--   This is the local analysis at a prime $q$ with $v_q(M)=2$ of the $\lambda$-adic representation attached to a weight-two newform whose associated automorphic vector admits no equivariant map to a principal series at $q$: inertia at $q$ acts, after an injective local extension of coefficients, with eigenvalues $a$ and $a^{-1}$, and the character $a$ is not killed by raising to the power $q-1$. It feeds the subsequent determination of the local type at $q$ (principal series versus supercuspidal) and the divisibility alternative $\lambda\mid q-1$ or $\lambda\mid q+1$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_exists_charpoly_inertia_eq_and_pow_sub_one_ne_one_of_forall_linearMap_psCarrier_eq_zero_of_factorization_eq_two_of_irreducible_odd_of_ne_two.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_sub_one_ne_one_of_forall_linearMap_psCarrier_eq_zero_of_factorization_eq_two_of_irreducible_odd_of_ne_two
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (hlam2 : lam ≠ 2)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* O')
    (ρ : GaloisRepAdic O')
    (hirrbar : ρ.residual.IsIrreducible) (hodd : ρ.residual.IsOdd)
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X
              + C ((ℓ : O')))
    (q : ℕ) [Fact q.Prime] (hqlam : q ≠ lam) (hqM : M.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (hps : ∀ (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
      (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) → f = 0) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsLocalRing O'') (j : O' →+* O'')
      (_ : IsLocalHom j) (_ : Function.Injective j)
      (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ),
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (LinearMap.charpoly (ρ.ρ σ)).map j =
            (X - C ((a σ : O''ˣ) : O'')) * (X - C (((a σ)⁻¹ : O''ˣ) : O''))) ∧
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∃ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q - 1) ≠ 1) := by sorry
