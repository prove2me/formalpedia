-- Prove2me | Theorems.Thm_CuspForm_AuxLevel_exists_linearEquiv_baseML_prod_ML
-- name    : CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/6299e633-0f5e-5efb-ad28-4cc7a5cf0913
-- title:
--   Auxiliary prime r: ML is two copies of baseML
-- statement:
--   Let $\mathcal O$ be a characteristic-zero discrete valuation domain, complete for its maximal-ideal adic topology and with finite residue field $k=\mathrm{ResidueField}\,\mathcal O$, and let $p$ be a prime with $p\in\mathfrak m_{\mathcal O}$. Let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $2$-dimensional $k$-space $V$ with a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k V$ factoring through a finite level, assumed absolutely irreducible (irreducible after base change to $\overline k$). Let $S$ be a finite set of naturals containing $p$, and $N\ge 1$ with every prime divisor of $N$ in $S$. Let $r$ be a prime with $r\notin S$, $r\nmid N$, $p\nmid r-1$, and such that for every valuation subring $P$ of $\overline{\mathbb Q}$ with $r$ in its nonunits and every $\sigma$ that is a Frobenius at $r$ for $P$ (lying in the decomposition subgroup and acting as $x\mapsto x^r$ on the residue field) one has $\mathrm{tr}\,\bar\rho(\sigma)^2\ne (r+1)^2$. Let $\theta$ be a ring homomorphism from the weight-two level-$N$ Hecke algebra [`CuspForm.heckeAlgebra N 2 S`](def/CuspForm_HeckeAlgebra.html#L18) to $k$ such that for each prime $\ell\nmid N$, $\ell\notin S$, and each $P$ over $\ell$ with Frobenius $\sigma$, the characteristic polynomial of $\bar\rho(\sigma)$ is $X^2-\theta(T_\ell)X+\ell$. Finally assume the hypotheses `BaseOpComm` and `OpComm`: the operators $\mathrm{baseOp}$ on [`CohCarrier.H1 N ⊤ 𝒪`](def/CohCarrier_Level.html#L162), respectively $\mathrm{op}$ on [`CuspForm.AuxLevel.Carrier N r 𝒪`](def/CuspForm_AuxLevelHeckeModule.html#L22), indexed by the generators $g\in$ `Gen N r S` (primes $\ell\notin S$ with $\ell\nmid N$, $\ell\ne r$), commute pairwise. Then there is an $\mathcal O$-linear equivalence $\Phi$ from the product of two copies of `baseML N r S 𝒪 θ hc₀` (the module attached to the base Hecke datum on [`CohCarrier.H1 N ⊤ 𝒪`](def/CohCarrier_Level.html#L162)) onto `ML N r S 𝒪 θ hc` (the module attached to the Hecke datum on the auxiliary-level carrier), equivariant for the generators: for every $g\in$ `Gen N r S` and every $m$, $\Phi(X_g\cdot m)=X_g\cdot\Phi(m)$, where $X_g$ is the corresponding variable of the common free polynomial algebra $\mathrm{MvPolynomial}(\mathrm{Gen}\,N\,r\,S)\,\mathcal O$ acting diagonally on the left.
--
--   This is the identification, at the level rigidified by an auxiliary prime $r$, of the localised cohomology of $\Gamma_0(N)\cap\Gamma_1(r)$ with two copies of that of $\Gamma_0(N)$, compatible with the anemic Hecke action away from $S\cup\{r\}$; it is the form of Ihara's lemma used in the Taylor–Wiles argument. It is cited by [`CuspForm.heckeLocal.exists_heckeModules_levelRaising_auxLevel_and_linearEquiv_ML_of_isEis_kernel_pair_of_not_cube_dvd`](thm.html#CuspForm.heckeLocal.exists_heckeModules_levelRaising_auxLevel_and_linearEquiv_ML_of_isEis_kernel_pair_of_not_cube_dvd) and by [`CuspForm.heckeLocal.free_of_linearEquiv_auxLevel_ML`](thm.html#CuspForm.heckeLocal.free_of_linearEquiv_auxLevel_ML), where it yields freeness of the auxiliary-level module over the local Hecke algebra of level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_AuxLevel_exists_linearEquiv_baseML_prod_ML.lean

import Definitions.Def_CuspForm_AuxLevelHeckeModuleBase
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hpS : p ∈ S)

    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)

    (r : ℕ) (hr : r.Prime) (hrS : r ∉ S) (hrN : ¬ r ∣ N) (hr1 : ¬ p ∣ r - 1)
    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (hc₀ : CuspForm.AuxLevel.BaseOpComm N r (↑S : Set ℕ) 𝒪)
    (hc : CuspForm.AuxLevel.OpComm N r (↑S : Set ℕ) 𝒪) :
    ∃ Φ : (CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀ ×
        CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀) ≃ₗ[𝒪]
        CuspForm.AuxLevel.ML N r (↑S : Set ℕ) 𝒪 θ hc,
      ∀ (g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ))
        (m : CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀ ×
          CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀),
        Φ ((MvPolynomial.X g : (CuspForm.AuxLevel.baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).FreeAlg) • m) =
          (MvPolynomial.X g : (CuspForm.AuxLevel.heckeData N r (↑S : Set ℕ) 𝒪 θ hc).FreeAlg) • Φ m := by sorry
