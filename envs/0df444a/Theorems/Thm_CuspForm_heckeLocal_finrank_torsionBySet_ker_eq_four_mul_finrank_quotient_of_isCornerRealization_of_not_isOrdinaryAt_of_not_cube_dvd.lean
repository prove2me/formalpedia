-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_finrank_torsionBySet_ker_eq_four_mul_finrank_quotient_of_isCornerRealization_of_not_isOrdinaryAt_of_not_cube_dvd
-- name    : CuspForm.heckeLocal.finrank_torsionBySet_ker_eq_four_mul_finrank_quotient_of_isCornerRealization_of_not_isOrdinaryAt_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/346c3293-c1f5-5b5b-8e26-27ffb4fb02ec
-- title:
--   Multiplicity four at p non-ordinary, cube-free level
-- statement:
--   Let $\mathcal O$ be a complete (adically complete for its maximal ideal) discrete valuation domain of characteristic zero with finite residue field, let $p$ be a prime with $p\neq 2$ whose image lies in the maximal ideal of $\mathcal O$, and let $\bar\rho$ be a two-dimensional residual Galois representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over the residue field of $\mathcal O$ which is absolutely irreducible (irreducible after base change to an algebraic closure). Let $S_{\min}\subseteq S$ be finite sets of primes with $p\in S_{\min}$, all elements of $S$ prime, such that for $q\neq p$ prime one has $q\in S_{\min}$ exactly when $\bar\rho$ is ramified at $q$ (i.e. some inertia element at some valuation subring of $\overline{\mathbb Q}$ over $q$ acts non-trivially), and such that for $q\in S_{\min}$, $q\neq p$, every inertia element at $q$ has characteristic polynomial $(X-1)^2$ in $\bar\rho$. Let $N,L\geq 1$ satisfy: all primes dividing $N$ lie in $S$; $p^2\nmid N$; every $q\in S_{\min}\setminus\{p\}$ divides $N$; every prime $q\neq p$ outside $S_{\min}$ dividing $N$ has $q^2\mid N$; no prime $q\neq p$ has $q^3\mid N$; $L\mid N$, $L$ has the same prime divisors as $N$, $q^2\mid N$ implies $q^2\mid L$, and $q^3\nmid L$ for all primes $q$; and assume weight-two cusp forms of level $\Gamma_0(N)$ are spanned over $\mathbb C$ by the integral lattice. Let $\theta$ be a ring homomorphism from the anemic Hecke algebra $\mathbb T =$ [`CuspForm.heckeAlgebra N 2 S`](def/CuspForm_HeckeAlgebra.html#L18) to the residue field of $\mathcal O$ such that for every prime $\ell\nmid N$, $\ell\notin S$, every valuation subring $P$ of $\overline{\mathbb Q}$ over $\ell$ and every Frobenius element $\sigma$ at $\ell$ for $P$, the characteristic polynomial of $\bar\rho(\sigma)$ is $X^2-\theta(T_\ell)X+\ell$. Let $M$ be a module over the localisation $T=$ [`CuspForm.heckeLocal N S 𝒪 θ`](def/CuspForm_HeckeLocal.html#L131) of $\mathbb T$, also an $\mathcal O$-module compatibly, equipped with an $\mathcal O$-bilinear form $B$, and assume the project's predicate [`CuspForm.heckeLocal.IsCornerRealization`](def/CuspForm_HeckeModuleCornerRealization.html#L19) for $p,\bar\rho,N,L,S,\theta,M,B$: there are a commuting family of Hecke operators on $H^1$ of level $L$ with coefficients in $\mathcal O$, a residual system of eigenvalues $\bar\theta$ on the generators, an idempotent splitting of the algebra they generate with a chosen corner index $i_0$ and an $\mathcal O$-algebra map from that corner ring to the residue field, such that all classes in the corner submodule are parabolic, $M$ is $\mathcal O$-linearly isomorphic to that corner submodule, $\bar\theta(T_\ell)=\theta(T_\ell)$ away from $S$, $L$ and $N$, $\bar\theta(U_q)=0$ whenever $q^2\mid L$, $\bar\theta(U_p)\neq 0$ whenever $\bar\rho$ is ordinary at $p$, the corner algebra map recovers $\bar\theta$ on generators, the isomorphism intertwines the $T_\ell$-action on $M$ with the Hecke operator on $H^1$, and $B$ is the pullback of the pairing [`CuspForm.Bfam₀`](def/CuspForm_CornerPairingFamily.html#L140) on parabolic classes. Finally let $\mathcal O'$ be a second complete discrete valuation domain of characteristic zero with finite residue field, module-finite over $\mathcal O$ by a local algebra map, let $\chi : T\to\mathcal O'$ be an $\mathcal O$-algebra homomorphism, and assume $p\mid L$ and $\bar\rho$ is not ordinary at $p$ (no line in the representation space is stable under some decomposition group at $p$ with inertia acting trivially on the quotient). Then the $\mathcal O$-rank of the submodule of $M$ annihilated by $\ker\chi$ equals $4$ times the $\mathcal O$-rank of $T/\ker\chi$.
--
--   This is the multiplicity statement used in the level-raising and Hecke-module comparison arguments: at a point $\chi$ of the localised anemic Hecke algebra, the $\chi$-eigenlattice inside a corner of the cohomology of level $L$ has rank exactly four times that of the corresponding quotient of the Hecke algebra, the factor four reflecting the two-dimensional local behaviour at $p$ (where $p\mid L$ and $\bar\rho$ is non-ordinary, so both $U_p$-eigenvalues degenerate) together with the cube-free level at the other primes. It feeds the construction of further corner realisations and the rank bounds used in comparing Hecke modules at minimal and non-minimal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_finrank_torsionBySet_ker_eq_four_mul_finrank_quotient_of_isCornerRealization_of_not_isOrdinaryAt_of_not_cube_dvd.lean

import Definitions.Def_CuspForm_HeckeModuleCornerRealization
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeLocal.finrank_torsionBySet_ker_eq_four_mul_finrank_quotient_of_isCornerRealization_of_not_isOrdinaryAt_of_not_cube_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S Smin : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)

    (N L : ℕ) [NeZero N] [NeZero L]
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNp : ¬ p ^ 2 ∣ N)
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hNunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ N → q ^ 2 ∣ N)
    (hN3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ N)
    (hLN : L ∣ N) (hNL : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ L)
    (hNL2 : ∀ q : ℕ, q.Prime → q ^ 2 ∣ N → q ^ 2 ∣ L) (hL3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ L)
    [Fact (CuspForm.HasIntegralStructure N 2)]

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪)
    (hM : CuspForm.heckeLocal.IsCornerRealization p ρbar N L (↑S : Set ℕ) θ M B)

    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (χ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪')
    (hcase : p ∣ L ∧ ¬ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p) :
    Module.finrank 𝒪
        ↥(Submodule.torsionBySet (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M ↑(RingHom.ker χ)) =
      4 * Module.finrank 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ ⧸ RingHom.ker χ) := by sorry
