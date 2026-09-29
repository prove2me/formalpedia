-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_charpoly_frobenius_eq_and_isRoot_charpoly_one_of_dvd_of_factorization_eq_conductor_factorization_of_not_sq_dvd
-- name    : CuspForm.IsPrimitiveForm.exists_galoisRepAdic_charpoly_frobenius_eq_and_isRoot_charpoly_one_of_dvd_of_factorization_eq_conductor_factorization_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/7f8ae134-d6e3-5cbb-9aff-d58bace4697e
-- title:
--   Newform λ-adic representation with inertia eigenvalue 1 at q ‖ M
-- statement:
--   Let $M \ge 1$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $h$ be a weight-two cusp form on $\Gamma_1(M)$ which is primitive for $\varepsilon$: its $q$-expansion satisfies $a_1(h)=1$, the Hecke relations $a_{pn}(h)+\varepsilon(p)\,p^{k-1}\,[p\mid n]\,a_{n/p}(h)=a_p(h)a_n(h)$ for primes $p \nmid M$, the relations $a_{\ell n}(h)=a_\ell(h)a_n(h)$ for primes $\ell \mid M$, and $h$ has nebentypus $\varepsilon$, while for no proper divisor $M' \mid M$ does the eigenpacket $(a_n(h), \varepsilon)$ occur in weight two at level $M'$. Let $\lambda$ be a prime and $S$ a finite set of naturals with $\lambda \in S$. Let $O'$ be a characteristic-zero discrete valuation domain, complete for the adic topology of its maximal ideal, with finite residue field and with $\lambda$ in its maximal ideal. The Hecke data are read in $O'$ through a commutative ring $R$, an injective ring homomorphism $\mathrm{toC} \colon R \to \mathbb{C}$, a ring homomorphism $\varphi \colon R \to O'$ and families $b, e \colon \mathbb{N} \to R$ with $\mathrm{toC}(b_\ell)=a_\ell(h)$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for all primes $\ell \nmid M$ with $\ell \notin S$. Let $q$ be a prime with $q \ne \lambda$, $q \mid M$, $q^2 \nmid M$, and $v_q(M) = v_q(\mathrm{cond}\,\varepsilon)$. Then there is a characteristic-zero discrete valuation domain $O''$, complete for its maximal-ideal-adic topology and with finite residue field, which is a module-finite $O'$-algebra whose structure map is local and injective, together with a $\lambda$-adic Galois representation $\rho$ over $O''$ — a free $O''$-module $V$ of rank two, finite over $O''$, and a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$) to $\mathrm{End}_{O''}(V)$ which is adically continuous in the sense that for each $n$ some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ has the property that elements fixing it act trivially on $V$ modulo $\mathfrak{m}^n V$ — such that: (i) for every prime $\ell \nmid M$ with $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\sigma$ in the decomposition group of $A$ acting on the residue field of $A$ by $x \mapsto x^\ell$, the characteristic polynomial of $\rho(\sigma)$ equals $X^2 - \varphi(b_\ell)X + \varphi(e_\ell)\ell$, the coefficients taken in $O''$; and (ii) for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$ and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$, the characteristic polynomial of $\rho(\sigma)$ has $1$ as a root.
--
--   This is the construction of the $\lambda$-adic representation attached to a weight-two primitive form, together with the local information at a prime $q$ exactly dividing the level whose valuation on the level agrees with its valuation on the conductor of the nebentypus: the ramified principal series case, in which inertia at $q$ acts with an eigenvalue equal to $1$. The extra hypothesis $q^2 \nmid M$ restricts the general statement to $v_q(M)=1$; it feeds the lemma [`CuspForm.IsEigenformWith.isRoot_charpoly_one_of_mem_inertiaSubgroupIn_of_factorization_eq_one_of_conductor_factorization_eq_one`](thm.html#CuspForm.IsEigenformWith.isRoot_charpoly_one_of_mem_inertiaSubgroupIn_of_factorization_eq_one_of_conductor_factorization_eq_one), part of the local analysis used for level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_charpoly_frobenius_eq_and_isRoot_charpoly_one_of_dvd_of_factorization_eq_conductor_factorization_of_not_sq_dvd.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsPrimitiveForm.exists_galoisRepAdic_charpoly_frobenius_eq_and_isRoot_charpoly_one_of_dvd_of_factorization_eq_conductor_factorization_of_not_sq_dvd
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
    (q : ℕ) [Fact q.Prime] (hqlam : q ≠ lam) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hMq : M.factorization q = ε.conductor.factorization q) :
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
        (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, (LinearMap.charpoly (ρ.ρ σ)).IsRoot 1) := by sorry
