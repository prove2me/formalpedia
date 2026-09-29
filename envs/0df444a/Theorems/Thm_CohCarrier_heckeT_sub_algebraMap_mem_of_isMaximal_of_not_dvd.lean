-- Prove2me | Theorems.Thm_CohCarrier_heckeT_sub_algebraMap_mem_of_isMaximal_of_not_dvd
-- name    : CohCarrier.heckeT_sub_algebraMap_mem_of_isMaximal_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/ec339bd6-7cd4-5e41-b680-26d765119742
-- title:
--   Residual Tₚ is the Frobenius trace on inertia coinvariants
-- statement:
--   Let $\mathcal{O}$ be a characteristic-zero complete discrete valuation ring (a domain, adically complete for its maximal ideal) with finite residue field $k$, let $p$ be a prime with $p \neq 2$ and $p \in \mathfrak{m}_{\mathcal{O}}$, and let $\bar\rho$ be a residual Galois representation over $k$ (a two-dimensional $k$-space $V$ with a monoid homomorphism $\bar\rho$ from $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\operatorname{End}_k V$ factoring through a finite level) which is absolutely irreducible, i.e. irreducible after base change to $\overline{k}$. Let $M \geq 1$ and let $S_0 \subseteq \mathbb{N}$ be finite, containing no prime divisor of $M$, with $p \nmid M$ and $p \notin S_0$; assume weight-$2$ cusp forms on $\Gamma_0(M)$ are spanned over $\mathbb{C}$ by those with integral $q$-expansion coefficients. On $H^1(\Gamma_0(M), \mathcal{O})$ consider the family of operators indexed by the generators $T_\ell$ ($\ell$ prime, $\ell \notin S_0$, $\ell \nmid M$), $U_q$ ($q$ prime, $q \mid M$) and $\langle d\rangle$ ($d \in (\mathbb{Z}/M)^\times$), assumed pairwise commuting, and let $\mathbb{T}$ be the $\mathcal{O}$-subalgebra of $\operatorname{End}_{\mathcal{O}}$ they generate. Let $\bar\theta$ assign a value in $k$ to each generator, and assume that for every prime $\ell \notin S_0$ with $\ell \nmid M$ and $\ell \neq p$, every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $P$ and every $\sigma$ that is a Frobenius at $\ell$ for $P$ (lying in the decomposition subgroup and acting as $x \mapsto x^{\ell}$ on the residue field of $P$), the characteristic polynomial of $\bar\rho(\sigma)$ is $X^2 - \bar\theta(T_\ell)X + \ell$. Let $\mathfrak{m}' \subseteq \mathbb{T}$ be a maximal ideal such that $T_\ell - c \in \mathfrak{m}'$ for every such $\ell$ and every $c \in \mathcal{O}$ with residue $\bar\theta(T_\ell)$. The conclusion: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ having $p$ as a nonunit, every Frobenius $\sigma$ at $p$ for $P$, and every $k$-linear endomorphism $E$ of the inertia coinvariants $V/\sum_{\tau \in I_P} \operatorname{im}(\bar\rho(\tau)-1)$ induced by $\bar\rho(\sigma)$ on classes, there is $c' \in \mathcal{O}$ whose residue is $\operatorname{tr}(E)$ and with $T_p - c' \in \mathfrak{m}'$.
--
--   This is the maximal-ideal formulation of the description of the residual eigenvalue of $T_p$ at a prime $p$ of good reduction for the Hecke system attached to $\bar\rho$: it is the trace of Frobenius on the inertia coinvariants at $p$ (the unit root of $X^2 - a_pX + p$ in the ordinary case, and $0$ when the coinvariants vanish). Because it quantifies over all maximal ideals lying over the prescribed residues of the $T_\ell$ with $\ell \neq p$ and allows arbitrary residue fields, it is the form used in [`CuspForm.heckeLocal.exists_corner_smul_eq_heckeT_residueChar_gammaZero`](thm.html#CuspForm.heckeLocal.exists_corner_smul_eq_heckeT_residueChar_gammaZero) to control $T_p$ on a local factor of the Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_sub_algebraMap_mem_of_isMaximal_of_not_dvd.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Trace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsLocalRing CohCarrier IharaLemma
open scoped IsMulCommutative in

theorem CohCarrier.heckeT_sub_algebraMap_mem_of_isMaximal_of_not_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (M : ℕ) [NeZero M] (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀M : ∀ q : ℕ, q.Prime → q ∣ M → q ∉ S₀)

    (hpM : ¬ p ∣ M) (hpS₀ : p ∉ S₀)
    [Fact (CuspForm.HasIntegralStructure M 2)]

    (hcomm : ∀ g h : CohCarrier.Gen M S₀,
      CohCarrier.opFamily M ⊤ S₀ 𝒪 g * CohCarrier.opFamily M ⊤ S₀ 𝒪 h =
        CohCarrier.opFamily M ⊤ S₀ 𝒪 h * CohCarrier.opFamily M ⊤ S₀ 𝒪 g)
    (θbar : CohCarrier.Gen M S₀ → ResidueField 𝒪)

    (hθbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS₀ : ℓ ∉ S₀) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θbar (CohCarrier.Gen.T ℓ hℓ hℓS₀ hℓM)) * X + C (ℓ : ResidueField 𝒪))

    (𝔪' : Ideal ↥(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra) (h𝔪' : 𝔪'.IsMaximal)
    (hover : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS₀ : ℓ ∉ S₀) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
      ∀ c : 𝒪, residue 𝒪 c = θbar (CohCarrier.Gen.T ℓ hℓ hℓS₀ hℓM) →
        (⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS₀ hℓM),
            Algebra.subset_adjoin (Set.mem_range_self _)⟩ - algebraMap 𝒪 _ c) ∈ 𝔪') :

    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[ResidueField 𝒪]
            (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)),
          (∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) →
            ∃ c' : 𝒪, residue 𝒪 c' = LinearMap.trace (ResidueField 𝒪) _ E ∧
              (⟨(CohCarrier.hdata M ⊤ S₀ 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.T p Fact.out hpS₀ hpM),
                  Algebra.subset_adjoin (Set.mem_range_self _)⟩ - algebraMap 𝒪 _ c') ∈ 𝔪' := by sorry
