-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_ordinaryLine_frobenius_sub_unitRoot_smul_mem_of_not_dvd
-- name    : CuspForm.IsPrimitiveForm.exists_galoisRepAdic_ordinaryLine_frobenius_sub_unitRoot_smul_mem_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/d87a28f5-51f8-5824-b017-bc4a62563f54
-- title:
--   Ordinary line of the λ-adic representation of a primitive form
-- statement:
--   Let $M\ge 1$, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb C$, and let $g$ be a weight-two cusp form on $\Gamma_1(M)$ which is primitive for $\varepsilon$: its first $q$-expansion coefficient is $1$, the Hecke relations $a_{pn}(g)+\varepsilon(p)p\,a_{n/p}(g)=a_p(g)a_n(g)$ hold for primes $p\nmid M$ (the second term read as $0$ when $p\nmid n$) and $a_{\ell n}(g)=a_\ell(g)a_n(g)$ for primes $\ell\mid M$, $g$ has nebentypus $\varepsilon$, and no eigenpacket with the coefficient system $(a_n(g))$ and character values $\varepsilon(n)$ occurs in weight two at any proper divisor $M'$ of $M$. Let $p$ be a prime with $p\nmid M$, let $S$ be a finite set of naturals with $p\in S$, and let $\mathcal O'$ be a characteristic-zero complete discrete valuation ring (domain, adically complete for its maximal ideal) with finite residue field and $p$ in its maximal ideal. Let $R$ be a commutative ring with an injective ring map $\mathrm{toC}\colon R\to\mathbb C$ and a ring map $\varphi\colon R\to\mathcal O'$, and let $b,e\colon\mathbb N\to R$, $b_p,e_p\in R$ satisfy $\mathrm{toC}(b_\ell)=a_\ell(g)$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for all primes $\ell\nmid M$ with $\ell\notin S$, together with $\mathrm{toC}(b_p)=a_p(g)$ and $\mathrm{toC}(e_p)=\varepsilon(p)$. Finally let $\alpha\in\mathcal O'$ be a unit with $\alpha^2-\varphi(b_p)\alpha+\varphi(e_p)p=0$. Then there is a characteristic-zero complete discrete valuation ring $\mathcal O''$ with finite residue field, an $\mathcal O'$-algebra which is finite as an $\mathcal O'$-module and whose structure map is local and injective, and a two-dimensional adically continuous Galois representation $\rho$ over $\mathcal O''$ (a free $\mathcal O''$-module $V$ of rank two with a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_{\mathcal O''}(V)$, continuous in the sense that for each $n$ some finite subextension acts trivially modulo $\mathfrak m^n V$) such that: for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ in the decomposition group of $A$ inducing $x\mapsto x^\ell$ on the residue field of $A$, the characteristic polynomial of $\rho(\sigma)$ is $X^2-\varphi(b_\ell)X+\varphi(e_\ell)\ell$ pushed to $\mathcal O''$; and for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$ there is an $\mathcal O''$-submodule $L\subseteq V$ which is spanned by the first member of some $\mathcal O''$-basis of $V$, is stable under the decomposition group of $P$, satisfies $\rho(\tau)v-v\in L$ for all $v\in V$ and all $\tau$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup at $P$, and satisfies $\rho(\sigma)v-\alpha v\in L$ for all $v\in V$ and every $\sigma$ inducing $x\mapsto x^p$ on the residue field of $P$ from its decomposition group.
--
--   This is the ordinarity statement for the $\lambda$-adic representation attached to a weight-two primitive form at a prime $p$ not dividing the level: the representation is unramified outside the level and the exceptional set with the expected Frobenius characteristic polynomials $X^2-a_\ell X+\varepsilon(\ell)\ell$, and at $p$ it has a Galois-stable line on which inertia acts trivially modulo the line and Frobenius acts by the chosen unit root $\alpha$ of $X^2-a_p X+\varepsilon(p)p$ on the quotient. It feeds the corresponding statement for eigenforms of level divisible by $p$ whose conductor is not divisible by $p^2$, and thence the ordinary modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_ordinaryLine_frobenius_sub_unitRoot_smul_mem_of_not_dvd.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsPrimitiveForm.exists_galoisRepAdic_ordinaryLine_frobenius_sub_unitRoot_smul_mem_of_not_dvd
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hg : CuspForm.IsPrimitiveForm ε g)
    (p : ℕ) [Fact p.Prime] (S : Finset ℕ) (hpS : p ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hpO' : (p : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R) (bp ep : R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff g ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (hbp : toC bp = ModularFormClass.qCoeff g p) (hep : toC ep = ε (p : ZMod M))
    (hpM : ¬ p ∣ M)
    (α : O') (hαu : IsUnit α) (hα : α * α - φ bp * α + φ ep * (p : O') = 0) :
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
              ∀ v : ρ.V, ρ.ρ σ v - algebraMap O' O'' α • v ∈ L) := by sorry
