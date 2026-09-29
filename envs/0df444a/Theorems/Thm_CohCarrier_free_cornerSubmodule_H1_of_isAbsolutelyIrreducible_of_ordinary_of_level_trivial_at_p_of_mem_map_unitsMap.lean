-- Prove2me | Theorems.Thm_CohCarrier_free_cornerSubmodule_H1_of_isAbsolutelyIrreducible_of_ordinary_of_level_trivial_at_p_of_mem_map_unitsMap
-- name    : CohCarrier.free_cornerSubmodule_H1_of_isAbsolutelyIrreducible_of_ordinary_of_level_trivial_at_p_of_mem_map_unitsMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/5c01376c-7822-5053-91f5-58ba3070ce9c
-- title:
--   Freeness of an ordinary Hecke corner of H¹
-- statement:
--   Let $\mathcal{O}$ be a characteristic-zero discrete valuation ring (a domain), $k$ a field that is an $\mathcal{O}$-algebra with $\mathcal{O}\to k$ surjective, $p\neq 2$ a prime with $k$ of characteristic $p$, and $M'\neq 0$ a natural number with $p\mid M'$ and $p^2\nmid M'$. Let $H'\le(\mathbb{Z}/M')^\times$ contain every unit whose image under the reduction $(\mathbb{Z}/M')^\times\to(\mathbb{Z}/(M'/p))^\times$ is trivial, and let $S$ be a finite set of naturals. On $H^1(M',H';\mathcal{O})$, the $\mathcal{O}$-module of additive homomorphisms from the additivisation of $\Gamma_{H'}(M')$ to $\mathcal{O}$, consider the operators [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91) indexed by the generators $T_\ell$ ($\ell$ prime, $\ell\notin S$, $\ell\nmid M'$), $U_q$ ($q$ prime, $q\mid M'$) and $\langle d\rangle$ ($d\in(\mathbb{Z}/M')^\times$), assumed pairwise commuting (`hcomm`), and let $\mathbb{T}$ be the $\mathcal{O}$-subalgebra of $\mathrm{End}_{\mathcal{O}}$ they generate. Given $\bar\theta$ assigning to each generator an element of $k$, an [`IharaLemma.IdempotentSplitting`](def/IharaLemma_IdempotentSplitting.html#L7) $S'$ of $\mathbb{T}$ (a complete orthogonal family of idempotents $e_i$ together with maximal ideals $\mathfrak{m}_i$ exhausting the maximal ideals and satisfying $e_i\in\mathfrak{m}_j\iff i\neq j$), an index $i_0'$ and an $\mathcal{O}$-algebra map $\pi_k$ from the corner ring $e_{i_0'}\mathbb{T}e_{i_0'}$ to $k$ sending the corner image $e_{i_0'}T_ge_{i_0'}$ of each Hecke operator to $\bar\theta(g)$, assume: $\bar\theta(U_p)\neq 0$; $\bar\rho$ is a two-dimensional residual representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $k$ factoring through a finite level, absolutely irreducible (irreducible after base change to $\overline{k}$), ordinary at $p$ in the sense that for each valuation subring $P$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit there is a free rank-one submodule, spanned by a basis vector, stable under the decomposition subgroup and on whose quotient the inertia subgroup acts trivially; $p$-distinguished, i.e. for some such $P$ and some $\sigma$ in its decomposition subgroup the characteristic polynomial of $\bar\rho(\sigma)$ is $(X-\alpha)(X-\beta)$ with $\alpha\neq\beta$ in $k$; and $\mathrm{tr}\,\bar\rho(\sigma)=\bar\theta(T_\ell)$ for every prime $\ell\notin S$ with $\ell\nmid M'$, every valuation subring over $\ell$ and every Frobenius element $\sigma$ at $\ell$ for it. Assume finally that $d\in(\mathbb{Z}/M')^\times$ has image the class of $p$ in $\mathbb{Z}/(M'/p)$ and that the image of $d$ in $(\mathbb{Z}/(M'/p))^\times$, or its negative, lies in the image of $H'$. Then the corner submodule $e_{i_0'}H^1(M',H';\mathcal{O})$, the range of multiplication by $e_{i_0'}$, is free as a module over the corner ring $e_{i_0'}\mathbb{T}e_{i_0'}$.
--
--   This is the freeness (multiplicity-one) statement for an ordinary component of weight-two cohomology in the case where $p$ exactly divides the level and there is no level structure at $p$, with the extra diamond-operator condition at $p$ expressed through the unit $d$; it is the form used at the Fermat application, where the level is of $\Gamma_0$-type at $p$. It feeds [`CohCarrier.free_sigmaCorner_gammaZero`](thm.html#CohCarrier.free_sigmaCorner_gammaZero) and [`CuspForm.AuxLevel.baseML_free_range_lsmul`](thm.html#CuspForm.AuxLevel.baseML_free_range_lsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_free_cornerSubmodule_H1_of_isAbsolutelyIrreducible_of_ordinary_of_level_trivial_at_p_of_mem_map_unitsMap.lean

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped IsMulCommutative in

theorem CohCarrier.free_cornerSubmodule_H1_of_isAbsolutelyIrreducible_of_ordinary_of_level_trivial_at_p_of_mem_map_unitsMap
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (M' : ℕ) [NeZero M'] (hpM : p ∣ M') (hpM2 : ¬ p ^ 2 ∣ M') (H' : Subgroup (ZMod M')ˣ)

    (hH'p : ∀ u : (ZMod M')ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H')
    (S : Finset ℕ)
    (hcomm : ∀ g h : CohCarrier.Gen M' ↑S,
      CohCarrier.opFamily M' H' ↑S 𝒪 g * CohCarrier.opFamily M' H' ↑S 𝒪 h =
        CohCarrier.opFamily M' H' ↑S 𝒪 h * CohCarrier.opFamily M' H' ↑S 𝒪 g)
    (θbar : CohCarrier.Gen M' ↑S → k)
    (S' : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata M' H' ↑S 𝒪 k hcomm θbar).opSubalgebra)
    (i₀' : Fin S'.n) (πk : S'.CornerRing i₀' →ₐ[𝒪] k)
    (hπk : ∀ g : CohCarrier.Gen M' ↑S, πk (S'.toCornerRing i₀'
      ⟨(CohCarrier.hdata M' H' ↑S 𝒪 k hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hord : θbar (CohCarrier.Gen.U p Fact.out hpM) ≠ 0)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (hordbar : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)

    (hdist : ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p ∧
      ∃ σ ∈ P.decompositionSubgroup ℚ, ∃ α β : k, α ≠ β ∧
        LinearMap.charpoly (ρbar.ρ σ) = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β))
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM))

    (d : (ZMod M')ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M' / p))ˣ) : ZMod (M' / p)) = (p : ZMod (M' / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ H'.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)) ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ H'.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) :
    Module.Free (S'.CornerRing i₀')
      ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀')) := by sorry
