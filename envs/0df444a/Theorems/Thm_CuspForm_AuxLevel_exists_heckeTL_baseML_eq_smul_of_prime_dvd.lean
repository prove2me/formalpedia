-- Prove2me | Theorems.Thm_CuspForm_AuxLevel_exists_heckeTL_baseML_eq_smul_of_prime_dvd
-- name    : CuspForm.AuxLevel.exists_heckeTL_baseML_eq_smul_of_prime_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/b55498c7-a685-5a26-9bd4-383eeca50f64
-- title:
--   At minimal level U_q acts by ± 1 on localised cohomology
-- statement:
--   Let $\mathcal O$ be a characteristic-zero complete discrete valuation ring with finite residue field $k=\mathrm{ResidueField}\,\mathcal O$, and let $p$ be an odd prime lying in the maximal ideal of $\mathcal O$. Let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $2$-dimensional $k$-space with an action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ factoring through a finite extension of $\mathbb Q$, assumed absolutely irreducible (its base change to $\overline k$ has no proper nonzero invariant subspace). Let $S_{\min}\subseteq S$ be finite sets of natural numbers with all elements of $S$ prime and $p\in S_{\min}$, such that for a prime $q\neq p$ one has $q\in S_{\min}$ exactly when $\bar\rho$ is ramified at $q$ (some valuation subring $P$ of $\overline{\mathbb Q}$ with $q\in P^{\mathrm{nonunits}}$ carries an inertia element acting non-trivially), and such that for $q\in S_{\min}$, $q\neq p$, every inertia element at $q$ has characteristic polynomial $(X-1)^2$ on $\bar\rho$. Let $N\neq 0$ be squarefree, with every prime divisor in $S$, divisible by every $q\in S_{\min}\setminus\{p\}$, every prime divisor $\neq p$ lying in $S_{\min}$, and such that if $p\mid N$ then $\bar\rho$, viewed as an adic representation over $k$, is not finite flat at $p$ in the sense of `GaloisRep.IsFlatAt`. Let $r$ be a natural number and let $\theta$ be a ring homomorphism from the weight-two level-$N$ Hecke algebra with $S$ omitted to $k$ such that for every prime $\ell\nmid N$ with $\ell\notin S$, every valuation subring $P$ of $\overline{\mathbb Q}$ over $\ell$ and every Frobenius element $\sigma$ at $\ell$ for $P$, the characteristic polynomial of $\bar\rho(\sigma)$ is $X^2-\theta(T_\ell)X+\ell$. Assume finally `BaseOpComm N r S 𝒪`: the operators $\mathrm{heckeTL}$ attached to the generators `Gen N r S` commute pairwise on $H^1(N,\top;\mathcal O)=\mathrm{Hom}(\Gamma_H(N)^{\mathrm{add}},\mathcal O)$. Then for every prime $q$ dividing $N$ there exists $\varepsilon\in\mathcal O$ with $\varepsilon=1$ or $\varepsilon=-1$ such that, for all $v\in H^1(N,\top;\mathcal O)$ and all $s$ in the complement of the prime $\mathfrak m_\theta=\ker\big(\mathcal O[X_g:g\in \mathrm{Gen}\,N\,r\,S]\to k,\ X_g\mapsto\theta(T_{g.\ell})\big)$, the fraction $\mathrm{heckeTL}\,N\,\top\,\mathcal O\,q\,(v)/s$ equals $\varepsilon\cdot(v/s)$ in the localisation `baseML N r S 𝒪 θ hc₀` of $H^1(N,\top;\mathcal O)$ at $\mathfrak m_\theta$.
--
--   This is the cohomological form, at minimal level, of the assertion that on the $\bar\rho$-part the operator $U_q$ for $q\mid N$ acts as an involution, with eigenvalue $+1$ or $-1$ uniform on the whole localised module; here $\mathrm{heckeTL}$ is the corestriction operator on group cohomology of $\Gamma_0(N)$, and the localisation is taken at the maximal ideal cut out by $\theta$ on the anemic polynomial algebra. It is used in the analysis of `baseML` as a module over the free algebra, in [`CuspForm.AuxLevel.baseML_free_range_lsmul`](thm.html#CuspForm.AuxLevel.baseML_free_range_lsmul) and in the comparison of the corner submodule of `baseML` with the localised cohomology at auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_AuxLevel_exists_heckeTL_baseML_eq_smul_of_prime_dvd.lean

import Mathlib.Algebra.Algebra.Tower
import Definitions.Def_CuspForm_AuxLevelHeckeModuleBase
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.AuxLevel.exists_heckeTL_baseML_eq_smul_of_prime_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hN : Squarefree N ∧ ∀ q : ℕ, q.Prime → q ≠ p → q ∣ N → q ∈ Smin)
    (hguard : p ∣ N → ¬ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsFlatAt p)

    (r : ℕ)

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (hc₀ : CuspForm.AuxLevel.BaseOpComm N r (↑S : Set ℕ) 𝒪) :
    ∀ (q : ℕ) [NeZero q], q.Prime → q ∣ N →
      ∃ ε : 𝒪, (ε = 1 ∨ ε = -1) ∧
        ∀ (v : CohCarrier.H1 N ⊤ 𝒪)
          (s : ↥(CuspForm.AuxLevel.baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).mTheta.primeCompl),
          (LocalizedModule.mk (CohCarrier.heckeTL N ⊤ 𝒪 q v) s :
              CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀) =
            ε • (LocalizedModule.mk v s : CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀) := by sorry
