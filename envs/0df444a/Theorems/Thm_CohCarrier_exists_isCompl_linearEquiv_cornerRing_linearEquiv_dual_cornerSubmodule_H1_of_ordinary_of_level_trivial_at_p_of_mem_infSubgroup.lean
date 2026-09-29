-- Prove2me | Theorems.Thm_CohCarrier_exists_isCompl_linearEquiv_cornerRing_linearEquiv_dual_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
-- name    : CohCarrier.exists_isCompl_linearEquiv_cornerRing_linearEquiv_dual_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/f6c36542-f3a9-5513-aa1e-a3f18707eb8b
-- title:
--   Ordinary p-distinguished corner of H¹: free line plus 𝒪-dual
-- statement:
--   Let $\mathcal{O}$ be a characteristic-zero discrete valuation domain, $k$ a field which is an $\mathcal{O}$-algebra with surjective structure map, $p$ an odd prime with $\operatorname{char} k = p$, and $M'$ a nonzero natural number with $p \mid M'$ and $p^2 \nmid M'$. Let $H' \le (\mathbb{Z}/M')^\times$ contain every unit reducing to $1$ in $(\mathbb{Z}/(M'/p))^\times$, and let $d \in (\mathbb{Z}/M')^\times$ have image in $\mathbb{Z}/(M'/p)$ equal to the class of $p$, with the image of $d$ or of $-d$ lying in [`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H'$ in $(\mathbb{Z}/(M'/p))^\times$. Let $S$ be a finite set of naturals and $\mathbb{T}$ a commutative $\mathcal{O}$-algebra acting on $H^1 = \operatorname{Hom}(\Gamma_{H'}(M')^{\mathrm{ab}}, \mathcal{O})$, compatibly with the $\mathcal{O}$-action and faithfully (only $0$ annihilates all of $H^1$), together with $\mathrm{op} \colon \mathrm{Gen}\,M'\,S \to \mathbb{T}$ whose values act as the operators [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91) attached to the generator symbols $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M'$), $U_q$ ($q$ prime dividing $M'$) and $\langle d \rangle$, with $\mathcal{O}[\operatorname{range}\mathrm{op}] = \mathbb{T}$. Let $\bar\theta \colon \mathrm{Gen}\,M'\,S \to k$, let $S'$ be an idempotent splitting of $\mathbb{T}$ (complete orthogonal idempotents $e_i$ matched bijectively with the maximal ideals $\mathfrak{m}_i$ by $e_i \in \mathfrak{m}_j \iff i \ne j$), fix $i_0$, and let $\pi_k \colon A := e_{i_0}\mathbb{T}e_{i_0} \to k$ be an $\mathcal{O}$-algebra map sending the corner $e_{i_0}\,\mathrm{op}(g)\,e_{i_0}$ to $\bar\theta(g)$. Assume $\bar\theta(U_p) \ne 0$; let $\bar\rho$ be a two-dimensional residual Galois representation over $k$ that is absolutely irreducible, ordinary at $p$ in the sense of [`GaloisRepAdic.IsOrdinaryAt`](def/GaloisRep_LocalConditions.html#L13) (for every valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ a line spanned by a basis vector is stable under the decomposition group and inertia acts trivially modulo it), $p$-distinguished (for some valuation subring over $p$ and some $\sigma$ in its decomposition group the characteristic polynomial of $\bar\rho(\sigma)$ is $(X-\alpha)(X-\beta)$ with $\alpha \ne \beta$), and such that for every prime $\ell \notin S$ with $\ell \nmid M'$ and every Frobenius element at $\ell$ the trace of $\bar\rho$ equals $\bar\theta(T_\ell)$. Then the corner submodule $e_{i_0} \cdot H^1$ has two complementary $A$-submodules $X$ and $Y$ with $X \cong A$ as $A$-modules, and there is an $\mathcal{O}$-linear isomorphism $\Phi \colon Y \xrightarrow{\sim} \operatorname{Hom}_{\mathcal{O}}(A, \mathcal{O})$ satisfying $\Phi(a \cdot y)(t) = \Phi(y)(at)$ for all $a, t \in A$ and $y \in Y$, i.e. an isomorphism of $A$-modules onto the $\mathcal{O}$-dual of $A$.
--
--   This is the structural description of the $p$-ordinary, $p$-distinguished local factor of the weight-two cohomology of $\Gamma_{H'}(M')$ with $p$ exactly dividing $M'$, in the form used by Wiles (§2.1 of his 1995 paper, Theorem 2.1(ii) and Lemma 2.2): after localising at the maximal ideal cut out by $\bar\theta$, the cohomology splits as a free module of rank one over the corner Hecke ring plus a copy of its $\mathcal{O}$-dual. The extra hypothesis that the class of $p$ lies in $\pm H'$ is what makes the Eichler–Shimura relation read $U_p = F$ on the component through the cusp $\infty$. It feeds the generation statement [`CohCarrier.exists_span_pair_union_ker_smul_eq_top_cornerSubmodule_H1_of_isAbsolutelyIrreducible_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup`](thm.html#CohCarrier.exists_span_pair_union_ker_smul_eq_top_cornerSubmodule_H1_of_isAbsolutelyIrreducible_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_isCompl_linearEquiv_cornerRing_linearEquiv_dual_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_isCompl_linearEquiv_cornerRing_linearEquiv_dual_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (M' : ℕ) [NeZero M'] (hpM : p ∣ M') (hpM2 : ¬ p ^ 2 ∣ M') (H' : Subgroup (ZMod M')ˣ)
    (hH'p : ∀ u : (ZMod M')ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H')
    (d : (ZMod M')ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M' / p))ˣ) : ZMod (M' / p)) = (p : ZMod (M' / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M' H' hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M' H' hpM)
    (S : Finset ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 M' H' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 M' H' 𝒪)]
    (hfaith : ∀ t : 𝕋, (∀ v : CohCarrier.H1 M' H' 𝒪, t • v = 0) → t = 0)
    (op : CohCarrier.Gen M' ↑S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M' ↑S) (v : CohCarrier.H1 M' H' 𝒪),
      op g • v = CohCarrier.opFamily M' H' ↑S 𝒪 g v)
    (hgen : Algebra.adjoin 𝒪 (Set.range op) = ⊤)
    (θbar : CohCarrier.Gen M' ↑S → k)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n) (πk : S'.CornerRing i₀ →ₐ[𝒪] k)
    (hπk : ∀ g : CohCarrier.Gen M' ↑S, πk (S'.toCornerRing i₀ (op g)) = θbar g)
    (hord : θbar (CohCarrier.Gen.U p Fact.out hpM) ≠ 0)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (hordbar : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (hdist : ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p ∧
      ∃ σ ∈ P.decompositionSubgroup ℚ, ∃ α β : k, α ≠ β ∧
        LinearMap.charpoly (ρbar.ρ σ) = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β))
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) :
    ∃ X Y : Submodule (S'.CornerRing i₀)
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
      IsCompl X Y ∧ Nonempty (↥X ≃ₗ[S'.CornerRing i₀] S'.CornerRing i₀) ∧
      ∃ Φ : ↥Y ≃ₗ[𝒪] (S'.CornerRing i₀ →ₗ[𝒪] 𝒪),
        ∀ (a : S'.CornerRing i₀) (y : ↥Y) (t : S'.CornerRing i₀), Φ (a • y) t = Φ y (a * t) := by sorry
