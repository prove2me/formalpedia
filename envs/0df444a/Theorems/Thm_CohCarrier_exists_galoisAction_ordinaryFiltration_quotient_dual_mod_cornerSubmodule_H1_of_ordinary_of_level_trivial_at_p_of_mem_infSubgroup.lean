-- Prove2me | Theorems.Thm_CohCarrier_exists_galoisAction_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
-- name    : CohCarrier.exists_galoisAction_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/5ffc6b9a-1d4e-52fb-aac7-1e717acf2566
-- title:
--   Ordinary filtration mod r on a corner of H¹
-- statement:
--   Let $\mathcal{O}$ be a characteristic-zero discrete valuation domain, $k$ a field that is an $\mathcal{O}$-algebra with $\mathcal{O}\to k$ surjective, $p$ an odd prime with $\operatorname{char} k=p$, and $M'$ a nonzero natural number with $p\mid M'$ and $p^2\nmid M'$. Let $H'\le(\mathbb{Z}/M')^\times$ contain every unit whose image in $(\mathbb{Z}/(M'/p))^\times$ is $1$, and let $d\in(\mathbb{Z}/M')^\times$ have image in $\mathbb{Z}/(M'/p)$ equal to the class of $p$, with the image of $d$ or of $-d$ lying in [`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H'$ in $(\mathbb{Z}/(M'/p))^\times$. Let $S$ be a finite set of naturals. Let $\mathbb{T}$ be a commutative $\mathcal{O}$-algebra acting on $H^1=\operatorname{Hom}(\Gamma_{H'}(M')^{\mathrm{ab,add}},\mathcal{O})$ compatibly with $\mathcal{O}$, acting faithfully, together with $\mathrm{op}:\mathrm{Gen}\,M'\,S\to\mathbb{T}$ whose values act as the operators [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91) attached to the generators $T_\ell$ ($\ell$ prime, $\ell\notin S$, $\ell\nmid M'$), $U_q$ ($q\mid M'$ prime) and diamonds, with $\mathcal{O}[\operatorname{range}\mathrm{op}]=\mathbb{T}$. Let $\bar\theta:\mathrm{Gen}\,M'\,S\to k$, let $S'$ be an idempotent splitting of $\mathbb{T}$ (complete orthogonal idempotents $e_i$ indexed in bijection with the maximal ideals $\mathfrak{m}_i$, with $e_i\in\mathfrak{m}_j$ iff $i\ne j$), $i_0$ an index, $A=$ the corner ring $e_{i_0}\mathbb{T}e_{i_0}$, and $\pi:A\to k$ an $\mathcal{O}$-algebra map with $\pi$ of the corner of $\mathrm{op}(g)$ equal to $\bar\theta(g)$; assume $\bar\theta(U_p)\ne 0$. Let $\bar\rho$ be a two-dimensional residual Galois representation over $k$, absolutely irreducible, whose traces at Frobenius elements match $\bar\theta$: for every prime $\ell\notin S$ with $\ell\nmid M'$, every valuation subring $A_\ell$ of $\overline{\mathbb{Q}}$ with $\ell\in A_\ell^{\mathrm{nonunits}}$ and every $\sigma$ that is a Frobenius at $\ell$ for $A_\ell$, $\operatorname{tr}\bar\rho(\sigma)=\bar\theta(T_\ell)$. Finally let $P_\ell$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p\in P_\ell^{\mathrm{nonunits}}$, and $r\in\mathfrak{m}_{\mathcal{O}}$, $r\ne 0$. Then, writing $P=e_{i_0}\cdot H^1$ for the corner submodule, there exist a map $\rho$ from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathcal{O}$-linear endomorphisms of $P$, an $A$-submodule $E\subseteq P$, functions $\psi_E,\psi_0$ from the Galois group to $A$, and an $\mathcal{O}$-linear $\Phi:P\to\operatorname{Hom}_{\mathcal{O}}(A,\mathcal{O}/(r))$ such that: $\rho(1)v\equiv v$, $\rho(\sigma\tau)v\equiv\rho(\sigma)\rho(\tau)v$ and $\rho(\sigma)(av)\equiv a\,\rho(\sigma)v$ modulo $rP$ for all $\sigma,\tau$, $a\in A$, $v\in P$; $rP\subseteq E$; $\Phi$ is surjective with $\Phi(v)=0$ exactly for $v\in E$ and $\Phi(av)(t)=\Phi(v)(at)$; for $\sigma$ in the decomposition subgroup of $P_\ell$ over $\mathbb{Q}$, $\rho(\sigma)v\equiv\psi_E(\sigma)v$ modulo $rP$ for $v\in E$ and $\rho(\sigma)v-\psi_0(\sigma)v\in E$ for all $v$; for $\sigma$ in the image of the inertia subgroup, $\rho(\sigma)v-v\in E$; and for every $\sigma$ in the decomposition subgroup the characteristic polynomial of $\bar\rho(\sigma)$ equals $(X-\pi(\psi_E(\sigma)))(X-\pi(\psi_0(\sigma)))$.
--
--   This is the ordinary-filtration step in Wiles' analysis of the $p$-adic Galois action on a local factor of the weight-two cohomology of $\Gamma_{H'}(M')$ with $p$ exactly dividing the level: mod $r$ the corner module $P$ carries a Galois action with an invariant submodule $E$ on which the decomposition group at $p$ acts by $\psi_E$, quotient $\operatorname{Hom}_{\mathcal{O}}(A,\mathcal{O}/(r))$ on which inertia acts trivially and the decomposition group by $\psi_0$, the two characters lifting the eigenvalues of $\bar\rho$ on the decomposition group. It is the variant carrying the hypothesis that the class of $p$ lies in $\pm$ the image of $H'$ modulo $M'/p$, and it feeds the construction of the ordinary line inside the corner module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_galoisAction_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_galoisAction_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
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
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM))
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (r : 𝒪) (hr : r ∈ IsLocalRing.maximalIdeal 𝒪) (hr0 : r ≠ 0) :
    ∃ (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
          (↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)) →ₗ[𝒪]
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀))))
      (E : Submodule (S'.CornerRing i₀)
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))
      (ψE ψ0 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (Φ : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)) →ₗ[𝒪]
        (S'.CornerRing i₀ →ₗ[𝒪] 𝒪 ⧸ Ideal.span {r})),

      (∀ v, ∃ w, ρ 1 v = v + r • w) ∧
      (∀ σ τ v, ∃ w, ρ (σ * τ) v = ρ σ (ρ τ v) + r • w) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : S'.CornerRing i₀) v,
        ∃ w, ρ σ (a • v) = a • ρ σ v + r • w) ∧

      (∀ w, r • w ∈ E) ∧

      Function.Surjective Φ ∧ (∀ v, Φ v = 0 ↔ v ∈ E) ∧
      (∀ (a : S'.CornerRing i₀) (v : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))
        (t : S'.CornerRing i₀), Φ (a • v) t = Φ v (a * t)) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∀ v ∈ E, ∃ w, ρ σ v = ψE σ • v + r • w) ∧
      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∀ v, ρ σ v - ψ0 σ • v ∈ E) ∧
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ v, ρ σ v - v ∈ E) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ,
        LinearMap.charpoly (ρbar.ρ σ) =
          (Polynomial.X - Polynomial.C (πk (ψE σ))) * (Polynomial.X - Polynomial.C (πk (ψ0 σ)))) := by sorry
