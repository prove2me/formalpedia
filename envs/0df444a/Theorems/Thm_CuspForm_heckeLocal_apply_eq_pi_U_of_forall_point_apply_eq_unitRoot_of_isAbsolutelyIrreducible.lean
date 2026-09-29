-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible
-- name    : CuspForm.heckeLocal.apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/e871a72c-6585-5c51-9419-39c901605826
-- title:
--   Uₚ as the unit root in the localised Hecke algebra
-- statement:
--   Let $\mathcal{O}$ be a complete discrete valuation ring which is a domain of characteristic zero with finite residue field $k=\mathrm{ResidueField}\,\mathcal{O}$, let $p$ be an odd prime with $p\in\mathfrak m_{\mathcal O}$, and let $\bar\rho$ be a two-dimensional residual representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $k$ (a $k$-space $V$ of rank $2$ with a monoid homomorphism factoring through a finite extension of $\mathbb Q$) which is absolutely irreducible, i.e. $k^{\mathrm{alg}}\otimes_k V$ has no proper non-zero stable subspace. Let $S_0\subseteq S$ be finite sets of primes with $p\in S$, and $N\neq 0$ an integer all of whose prime divisors lie in $S$ and outside $S_0$, with $p^2\nmid N$, such that: $\bar\rho$ is unramified at each $q\in S$, $q\neq p$, $q\nmid N$; for each prime $q\neq p$ with $q\parallel N$, $\bar\rho$ is ramified at $q$ and every inertia element at $q$ has characteristic polynomial $(X-1)^2$; for each prime $q\neq p$ with $q^2\mid N$ one has $q^3\nmid N$ and the same unipotence on inertia at $q$; and if $p\mid N$ then $\bar\rho$ is ordinary at $p$ (at every valuation subring over $p$ there is a line spanned by a basis vector, stable under the decomposition group, modulo which inertia acts trivially). Assume weight-two cusp forms on $\Gamma_0(N)$ are spanned over $\mathbb C$ by forms with integral $q$-expansions. Let $\theta':\mathbb T^{S_0}(N)\to k$ be a ring homomorphism on the Hecke algebra generated over $\mathbb Z$ by the $T_\ell$ ($\ell$ prime, $\ell\nmid N$, $\ell\notin S_0$) and $U_q$ ($q$ prime, $q\mid N$, $q\notin S_0$), subject to: for $\ell\neq p$ prime, $\ell\nmid N$, $\ell\notin S_0$, and every valuation subring $P$ of $\overline{\mathbb Q}$ lying over $\ell$ and every Frobenius $\sigma$ at $\ell$ for $P$, the characteristic polynomial of $\bar\rho(\sigma)$ is $X^2-\theta'(T_\ell)X+\ell$; $\theta'(U_q)=0$ when $q^2\mid N$; $\theta'(U_q)$ equals the trace of the endomorphism induced by a Frobenius $\sigma$ at $q$ on the inertia coinvariants $V/\sum_{\tau\in I_P}\mathrm{im}(\bar\rho(\tau)-1)$ when $q\parallel N$; and the analogous trace formula for $\theta'(T_p)$ if $p\nmid N$, $p\notin S_0$. Let $\theta:\mathbb T^{S}(N)\to k$ be the composite of the inclusion $\mathbb T^{S}(N)\subseteq\mathbb T^{S_0}(N)$ with $\theta'$, and let $\Psi$ be an $\mathcal O$-algebra homomorphism from [`CuspForm.heckeLocal N S 𝒪 θ`](def/CuspForm_HeckeLocal.html#L131) to [`CuspForm.heckeLocal N S₀ 𝒪 θ'`](def/CuspForm_HeckeLocal.html#L131) compatible, via the canonical maps [`CuspForm.heckeLocal.π`](def/CuspForm_HeckeLocal.html#L151), with that inclusion. Assume further $p\mid N$ and $\theta'(U_p)\neq 0$. Let $u$ be an element of [`CuspForm.heckeLocal N S 𝒪 θ`](def/CuspForm_HeckeLocal.html#L131) with the following pointwise property: for every complete discrete valuation ring $\mathcal O'$ as above which is a finite $\mathcal O$-algebra with local structure map, every $\mathcal O$-algebra homomorphism $\psi$ to $\mathcal O'$, every $M\neq 0$ dividing $N$, every newform $g$ of weight $2$ on $\Gamma_0(M)$ (a normalised eigenform whose eigensystem away from $N$ occurs at no proper divisor of its level), every ring homomorphism $\chi_g:\mathbb T^{S\setminus\{p\}}(M)\to\mathbb C$ with $\chi_g(T_\ell)=a_\ell(g)$, and every ring homomorphism $\iota$ from the image of $\chi_g$ to $\mathcal O'$ with $\iota(\chi_g(T_\ell))=\psi(\pi(T_\ell))$ for all primes $\ell\nmid N$, $\ell\notin S$: if $p\mid M$ then $a_p(g)=\pm1$ and $\psi(u)$ is the image of the same sign in $\mathcal O'$; and if $p\nmid M$ and $\iota(\chi_g(T_p))$ is a unit, then $\psi(u)$ is a unit and $\psi(u)^2-\iota(\chi_g(T_p))\psi(u)+p=0$. Then $\Psi u$ equals the image of $U_p$ under [`CuspForm.heckeLocal.π N S₀ 𝒪 θ'`](def/CuspForm_HeckeLocal.html#L151).
--
--   This identifies an element of the localised Hecke algebra away from $S$, characterised by the unit-root (respectively $a_p=\pm1$) condition at every newform point, with the operator $U_p$ in the localised Hecke algebra away from $S_0$; it is the Atkin–Lehner and ordinary-unit-root input to the comparison of Hecke algebras at different auxiliary sets of primes, as in Darmon–Diamond–Taylor §4.1–4.2. It is used by [`CuspForm.heckeLocal.exists_apply_eq_pi_U_of_dvd_of_isOrdinaryAt_of_charpoly_frobenius_eq`](thm.html#CuspForm.heckeLocal.exists_apply_eq_pi_U_of_dvd_of_isOrdinaryAt_of_charpoly_frobenius_eq), and cites the existence of a newform attached to a point of the Hecke algebra together with the local-homomorphism and residue properties of points of [`CuspForm.heckeLocal`](def/CuspForm_HeckeLocal.html#L131).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S S₀ : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S) (hS₀ : S₀ ⊆ S)
    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNS₀ : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S₀) (hNp : ¬ p ^ 2 ∣ N)
    (hunr : ∀ q ∈ S, q ≠ p → ¬ q ∣ N → ρbar.IsUnramifiedAt q)
    (hst : ∀ q : ℕ, q.Prime → q ≠ p → q ∣ N → ¬ q ^ 2 ∣ N →
      ¬ ρbar.IsUnramifiedAt q ∧ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (hsq : ∀ q : ℕ, q.Prime → q ≠ p → q ^ 2 ∣ N →
      ¬ q ^ 3 ∣ N ∧ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (hord : p ∣ N → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ' : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* ResidueField 𝒪)

    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ (↑S₀ : Set ℕ)), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀)) * X + C (ℓ : ResidueField 𝒪))

    (hU0 : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), q ^ 2 ∣ N →
      θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0)

    (hU1 : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), ¬ q ^ 2 ∣ N →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
          ∀ E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[ResidueField 𝒪]
              (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)),
            (∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) →
              θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = LinearMap.trace (ResidueField 𝒪) _ E)

    (hTp : ∀ (hpN : ¬ p ∣ N) (hpS₀ : p ∉ (↑S₀ : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
          ∀ E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[ResidueField 𝒪]
              (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)),
            (∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) →
              θ' (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpN hpS₀) =
                LinearMap.trace (ResidueField 𝒪) _ E)

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
      θ t = θ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))
    (Ψ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] CuspForm.heckeLocal N (↑S₀ : Set ℕ) 𝒪 θ')
    (hΨ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
      Ψ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ t) =
        CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ'
          (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))
    (hpN : p ∣ N)
    (hθ'U : θ' (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpN (hNS₀ p Fact.out hpN)) ≠ 0)
    (u : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)
    (hu : ∀ (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
        [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
        [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
        (ψ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪')
        (M : ℕ) [NeZero M] (hMN : M ∣ N)
        (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), g.IsNewform →
        ∀ (chig : CuspForm.heckeAlgebra M 2 ((↑S : Set ℕ) \ {p}) →+* ℂ),
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
            chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ) →
        ∀ (iota : chig.range →+* 𝒪'),
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
              (fun h => hℓN (h.trans hMN)) (fun h => hℓS (Set.mem_of_mem_diff h)))) =
              ψ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) →
        (p ∣ M → ∃ a : ℤ, (a = 1 ∨ a = -1) ∧
          ModularFormClass.qCoeff g p = (a : ℂ) ∧ ψ u = (a : 𝒪')) ∧
        (∀ hpM : ¬ p ∣ M,
          IsUnit (iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpM
            (fun h => h.2 rfl)))) →
          IsUnit (ψ u) ∧
            ψ u * ψ u - iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpM
              (fun h => h.2 rfl))) * ψ u + (p : 𝒪') = 0)) :
    Ψ u = CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ'
      (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpN (hNS₀ p Fact.out hpN)) := by sorry
