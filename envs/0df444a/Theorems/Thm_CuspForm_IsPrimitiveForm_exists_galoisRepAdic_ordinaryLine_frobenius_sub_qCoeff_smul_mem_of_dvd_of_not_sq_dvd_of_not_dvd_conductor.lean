-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_ordinaryLine_frobenius_sub_qCoeff_smul_mem_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
-- name    : CuspForm.IsPrimitiveForm.exists_galoisRepAdic_ordinaryLine_frobenius_sub_qCoeff_smul_mem_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/6612efe1-4f02-5fe1-87e5-6dfef6fcdab4
-- title:
--   Ordinary line at p ‖ M for a weight-two primitive form
-- statement:
--   Let $M\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb C$, and let $g$ be a cusp form of weight $2$ on $\Gamma_1(M)$ which is primitive for $\varepsilon$: its $q$-coefficient at $1$ is $1$, it satisfies the Hecke recursions $a_{\ell n}+\varepsilon(\ell)\ell^{k-1}a_{n/\ell}=a_\ell a_n$ at primes $\ell\nmid M$ and $a_{\ell n}=a_\ell a_n$ at primes $\ell\mid M$, it has nebentypus $\varepsilon$, and its eigenpacket occurs at no proper divisor of $M$. Let $p$ be prime, $S$ a finite set of naturals, and $O'$ a characteristic-zero complete discrete valuation ring with finite residue field and $p$ in its maximal ideal. Let $R$ be a commutative ring with an injective ring homomorphism $\mathrm{toC}\colon R\to\mathbb C$ and a ring homomorphism $\varphi\colon R\to O'$, and let $b,e\colon\mathbb N\to R$, $b_p\in R$ satisfy $\mathrm{toC}(b_\ell)=a_\ell(g)$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for all primes $\ell\nmid M$ with $\ell\notin S$, and $\mathrm{toC}(b_p)=a_p(g)$. Assume $p\mid M$, $p^2\nmid M$ and $p\nmid\operatorname{cond}(\varepsilon)$. Then there is a characteristic-zero complete discrete valuation ring $O''$ with finite residue field, an $O'$-algebra which is finite as an $O'$-module with local and injective structure map, and a two-dimensional $\mathfrak m$-adically continuous Galois representation $\rho$ on a finite free $O''$-module $V$ of rank $2$ (a [`GaloisRepAdic O''`](def/GaloisRep_Adic.html#L16)) such that: for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $A$ and every $\sigma$ lying in the decomposition subgroup of $A$ and acting as $x\mapsto x^{\ell}$ on the residue field of $A$, the characteristic polynomial of $\rho(\sigma)$ is $X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$ (coefficients pushed to $O''$); and for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $P$ there is an $O''$-submodule $L\subseteq V$ spanned by the first member of some $O''$-basis of $V$ indexed by $\mathrm{Fin}\,2$, stable under the decomposition subgroup of $P$, such that $\rho(\tau)v-v\in L$ for every $\tau$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ and every $v\in V$, and $\rho(\sigma)v-\varphi(b_p)v\in L$ for every $v\in V$ and every $\sigma$ in the decomposition subgroup of $P$ acting as $x\mapsto x^{p}$ on the residue field.
--
--   This is the construction of the $\lambda$-adic representation attached to a weight-two newform whose level is exactly divisible by $p$ and whose nebentypus is unramified at $p$, together with the local description at $p$: a Galois-stable line on which the representation is unramified modulo it, with arithmetic Frobenius acting on the unramified quotient through $a_p(g)$. It is the input for the ordinary/multiplicative-reduction local analysis at $p$, and is used by [`GaloisRepAdic.exists_ordinaryLine_frobenius_sub_smul_mem_of_isEigenformWith_of_isUnit_of_dvd_of_not_sq_dvd_of_not_dvd_conductor`](thm.html#GaloisRepAdic.exists_ordinaryLine_frobenius_sub_smul_mem_of_isEigenformWith_of_isUnit_of_dvd_of_not_sq_dvd_of_not_dvd_conductor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_ordinaryLine_frobenius_sub_qCoeff_smul_mem_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsPrimitiveForm.exists_galoisRepAdic_ordinaryLine_frobenius_sub_qCoeff_smul_mem_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (p : ℕ) [Fact p.Prime] (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hpO' : (p : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R) (bp : R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (hbp : toC bp = ModularFormClass.qCoeff g p)
    (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M) (hpε : ¬ p ∣ ε.conductor) :
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
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∃ L : Submodule O'' ρ.V,
            (∃ bs : Module.Basis (Fin 2) O'' ρ.V, L = O'' ∙ bs 0) ∧
            (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
            (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
            (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
              ∀ v : ρ.V, ρ.ρ σ v - algebraMap O' O'' (φ bp) • v ∈ L) := by sorry
