-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_free_of_linearEquiv_auxLevel_ML
-- name    : CuspForm.heckeLocal.free_of_linearEquiv_auxLevel_ML
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/6efd4f18-8862-5346-ada7-02ee4f651765
-- title:
--   Freeness over the minimal-level local Hecke algebra at auxiliary level
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring of characteristic zero with finite residue field $k=\mathrm{ResidueField}\,\mathcal O$, and let $p$ be an odd prime with $p\in\mathfrak m_{\mathcal O}$. Let $\bar\rho$ be a two-dimensional residual Galois representation over $k$ which is absolutely irreducible (irreducible after base change to $\overline k$). Let $S,S_{\min}$ be finite sets of natural numbers with every element of $S$ prime, $p\in S_{\min}\subseteq S$, such that for primes $q\neq p$ one has $q\in S_{\min}$ exactly when $\bar\rho$ is ramified at $q$, and such that for $q\in S_{\min}$, $q\neq p$, every inertia element above $q$ has characteristic polynomial $(X-1)^2$ on $\bar\rho$. Let $N\neq 0$ satisfy: every prime divisor of $N$ lies in $S$; every $q\in S_{\min}$ with $q\neq p$ divides $N$; $N$ is squarefree and each prime $q\neq p$ dividing $N$ lies in $S_{\min}$; and if $p\mid N$ then $\bar\rho$, viewed as an adic representation over $k$, fails the finite-flat condition `IsFlatAt` at $p$. Let $r\geq 5$ be a prime with $r\notin S$, $r\nmid Np$, $p\nmid r-1$, and $\operatorname{tr}\bar\rho(\sigma)^2\neq (r+1)^2$ for every valuation subring $P$ of $\overline{\mathbb Q}$ lying over $r$ and every Frobenius element $\sigma$ at $r$ for $P$. Assume the weight-two cusp forms for $\Gamma_0(N)$ admit an integral structure, i.e. the forms with integral $q$-expansion coefficients span them over $\mathbb C$. Let $\theta$ be a ring homomorphism from the anemic Hecke algebra $\mathbb T=$ [`CuspForm.heckeAlgebra N 2 S`](def/CuspForm_HeckeAlgebra.html#L18) to $k$ such that for every prime $\ell$ with $\ell\nmid N$, $\ell\notin S$ and every Frobenius $\sigma$ at $\ell$ one has $\mathrm{charpoly}(\bar\rho(\sigma))=X^2-\theta(T_\ell)X+\ell$, and let $T=$ [`CuspForm.heckeLocal N S 𝒪 θ`](def/CuspForm_HeckeLocal.html#L131) be the associated local Hecke algebra, with structure map $\pi$, equipped with a datum `HeckeGaloisRepDatum` (structure map, residual compatibility, generation of $T$ over $\mathcal O$ by the image of $\pi$, liftability of $\mathcal O$-valued characters, surjectivity on residue fields, and a two-dimensional adic representation over $T$ with the prescribed Frobenius characteristic polynomials and absolutely irreducible reduction). Finally let $L$ be a $T$-module which is also an $\mathcal O$-module, compatibly via the scalar tower, finite and free over $\mathcal O$, let $hc$ assert that the operators attached to the generators `Gen N r S` (primes $\ell\notin S$ with $\ell\nmid N$, $\ell\neq r$) commute pairwise on $H^1$ of level $Nr$ with the subgroup `subgroup N r`, and let $eML$ be an $\mathcal O$-linear isomorphism of $L$ with the module [`CuspForm.AuxLevel.ML N r S 𝒪 θ hc`](def/CuspForm_AuxLevelHeckeModule.html#L46) attached to that Hecke datum, carrying the action of $\pi(T_\ell)$ for each generator $\ell$ to the action of the corresponding variable $X_\ell$ of the free polynomial algebra $\mathrm{MvPolynomial}(\mathrm{Gen}\,N\,r\,S,\mathcal O)$. Then $L$ is free as a $T$-module.
--
--   This is the multiplicity-one statement for the cohomology of the modular curve of level $\Gamma_0(N)\cap\Gamma_1(r)$, localised at the non-Eisenstein eigensystem $\theta$: any $\mathcal O$-finite free module identified with that cohomology compatibly with the Hecke action of the unramified generators is free over the local Hecke algebra of the minimal level $N$. It is used to transport freeness along an arbitrary Hecke–Galois datum, and is cited in the construction of the semilinear comparison maps used for the Taylor–Wiles modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_free_of_linearEquiv_auxLevel_ML.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_AuxLevelHeckeModule
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.free_of_linearEquiv_auxLevel_ML
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

    (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) (hrS : r ∉ S) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)
    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)
    [Fact (CuspForm.HasIntegralStructure N 2)]

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (Hn : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ))

    (L : Type) [AddCommGroup L] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) L] [Module 𝒪 L]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) L] [Module.Finite 𝒪 L] [Module.Free 𝒪 L]
    (hc : CuspForm.AuxLevel.OpComm N r (↑S : Set ℕ) 𝒪)
    (eML : L ≃ₗ[𝒪] CuspForm.AuxLevel.ML N r (↑S : Set ℕ) 𝒪 θ hc)
    (heML : ∀ (g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ)) (m : L),
      eML (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem) • m) =
        (MvPolynomial.X g : (CuspForm.AuxLevel.heckeData N r (↑S : Set ℕ) 𝒪 θ hc).FreeAlg) • eML m) :
    Module.Free (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) L := by sorry
