-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_finrank_torsionBySet_le_of_isCornerRealization_of_not_dvd_of_not_cube_dvd
-- name    : CuspForm.heckeLocal.finrank_torsionBySet_le_of_isCornerRealization_of_not_dvd_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/8797f245-96ca-5593-8216-37cc8a98a471
-- title:
--   Eigen-rank does not grow when raising the level by q²
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring of characteristic zero with finite residue field $k=\mathrm{ResidueField}(\mathcal O)$, let $p$ be an odd prime with $p\in\mathfrak m_{\mathcal O}$, and let $\bar\rho$ be a two-dimensional residual Galois representation over $k$ (a rank-two $k$-module with a $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$-action factoring through a finite level) that is absolutely irreducible. Let $S\supseteq S_{\min}$ be finite sets of primes with $p\in S_{\min}$, such that a prime $q'\neq p$ lies in $S_{\min}$ exactly when $\bar\rho$ is ramified at $q'$, and such that for $q'\in S_{\min}$, $q'\neq p$, every inertia element at $q'$ has characteristic polynomial $(X-1)^2$ on $\bar\rho$. Let $q\in S$ be a prime, $q\neq p$, with $q\nmid N$, and put $N'=Nq^2$, $L'=Lq^2$, where $N,L\geq 1$ satisfy: every prime divisor of $N$ lies in $S$; $p^2\nmid N$; every $q'\in S_{\min}\setminus\{p\}$ divides $N$; every prime $q'\neq p$ dividing $N$ but not in $S_{\min}$ has $q'^2\mid N$; no prime $q'\neq p$ has $q'^3\mid N$; $L\mid N$, $L$ and $N$ have the same prime divisors, $q'^2\mid N$ implies $q'^2\mid L$, and $L$ is cube-free. Assume the weight-two cusp forms for $\Gamma_0(N)$ and for $\Gamma_0(N')$ are spanned by their integral lattices. Let $\theta$ and $\theta'$ be ring homomorphisms to $k$ from the Hecke algebras $\mathbb T^S(N)$, $\mathbb T^S(N')$ generated over $\mathbb Z$ by the operators away from $S$, each realising $\bar\rho$ in the sense that for every prime $\ell\notin S$ not dividing the level and every Frobenius element $\sigma$ at $\ell$ (relative to a valuation subring of $\overline{\mathbb Q}$ over $\ell$) the characteristic polynomial of $\bar\rho(\sigma)$ is $X^2-\theta(T_\ell)X+\ell$, respectively with $\theta'$. Let $\pi_T\colon \mathbb T^S(N)_\theta\to\mathcal O$ and $\pi_{T'}\colon\mathbb T^S(N')_{\theta'}\to\mathcal O$ be $\mathcal O$-algebra maps on the localisations, agreeing on $T_\ell$ for all primes $\ell\notin S$ with $\ell\nmid N'$. Let $M$ be a $\mathbb T^S(N)_\theta$-module, finite and free over $\mathcal O$ with compatible scalars, carrying an $\mathcal O$-bilinear form $B$, and let $M'$ be a $\mathbb T^S(N')_{\theta'}$-module with compatible $\mathcal O$-structure and bilinear form $B'$ (finiteness and freeness over $\mathcal O$ are assumed of $M$ only). Assume $(M,B)$ is a corner realisation for $(p,\bar\rho,N,L,S,\theta)$ and $(M',B')$ one for $(p,\bar\rho,N',L',S,\theta')$: that is, there are a commuting family of Hecke and diamond operators on $H^1$ of level $L$ (resp. $L'$), a system of scalars $\bar\theta$ on the generators, an idempotent splitting of the subalgebra they generate, an index $i_0$ with corner ring mapping to $k$ by $g\mapsto\bar\theta(g)$, and an $\mathcal O$-linear isomorphism of $M$ (resp. $M'$) with the corresponding corner submodule of $H^1$, which consists of parabolic classes, such that the isomorphism intertwines the action of $T_\ell$ ($\ell\notin S$, $\ell$ not dividing the level) with the cohomological Hecke operator and carries $B$ to the pairing $\mathrm{Bfam}_0$, while $\bar\theta(T_\ell)=\theta(T_\ell)$ for $\ell\notin S$ prime to the levels, $\bar\theta(U_{q'})=0$ whenever $q'^2$ divides the cohomological level, and $\bar\theta(U_p)\neq 0$ if $p$ divides it and $\bar\rho$ is ordinary at $p$. The conclusion is that the $\mathcal O$-rank of the submodule of $M'$ annihilated by $\ker\pi_{T'}$ is at most the $\mathcal O$-rank of the submodule of $M$ annihilated by $\ker\pi_T$.
--
--   This is the comparison of multiplicities in a level-raising step at a prime $q\nmid N$, $q\neq p$, for cube-free levels away from $p$: passing from level $N$ to $Nq^2$ does not increase the rank of the $\pi$-eigencomponent of the Hecke module. It is obtained from the two multiplicity formulas for corner realisations (the factor-two formula at level $N$ and the factor-four formula at the raised level in the non-ordinary case), and it feeds the construction of the next rung of corner realisations used in the minimal-to-non-minimal level-raising induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_finrank_torsionBySet_le_of_isCornerRealization_of_not_dvd_of_not_cube_dvd.lean

import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CuspForm_HeckeModuleCornerRealization
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.finrank_torsionBySet_le_of_isCornerRealization_of_not_dvd_of_not_cube_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqS : q ∈ S)
    (N N' L L' : ℕ) [NeZero N] [NeZero N'] [NeZero L] [NeZero L'] [NeZero q]
    (hN' : N' = N * q ^ 2) (hL' : L' = L * q ^ 2) (hqN : ¬ q ∣ N)
    (hNS : ∀ q' : ℕ, q'.Prime → q' ∣ N → q' ∈ S)
    (hNp : ¬ p ^ 2 ∣ N)
    (hNmin : ∀ q' ∈ Smin, q' ≠ p → q' ∣ N)
    (hNunr : ∀ q' : ℕ, q'.Prime → q' ≠ p → q' ∉ Smin → q' ∣ N → q' ^ 2 ∣ N)
    (hN3 : ∀ q' : ℕ, q'.Prime → q' ≠ p → ¬ q' ^ 3 ∣ N)
    (hLN : L ∣ N) (hNL : ∀ q' : ℕ, q'.Prime → q' ∣ N → q' ∣ L)
    (hNL2 : ∀ q' : ℕ, q'.Prime → q' ^ 2 ∣ N → q' ^ 2 ∣ L) (hL3 : ∀ q' : ℕ, q'.Prime → ¬ q' ^ 3 ∣ L)
    [Fact (CuspForm.HasIntegralStructure N 2)] [Fact (CuspForm.HasIntegralStructure N' 2)]

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (θ' : CuspForm.heckeAlgebra N' 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (πT : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪)
    (πT' : CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ' →ₐ[𝒪] 𝒪)
    (hπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N),
      πT' (CuspForm.heckeLocal.π N' (↑S : Set ℕ) 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS)) =
        πT (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))

    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪)
    (hM : CuspForm.heckeLocal.IsCornerRealization p ρbar N L (↑S : Set ℕ) θ M B)

    (M' : Type) [AddCommGroup M'] [Module (CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ') M'] [Module 𝒪 M']
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ') M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪)
    (hM' : CuspForm.heckeLocal.IsCornerRealization p ρbar N' L' (↑S : Set ℕ) θ' M' B') :
    Module.finrank 𝒪 ((Submodule.torsionBySet (CuspForm.heckeLocal N' (↑S : Set ℕ) 𝒪 θ') M'
        ↑(RingHom.ker πT')).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M
        ↑(RingHom.ker πT)).restrictScalars 𝒪) := by sorry
