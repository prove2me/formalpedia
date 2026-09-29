-- Prove2me | Theorems.Thm_CohCarrier_exists_galoisAction_ordinaryLine_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
-- name    : CohCarrier.exists_galoisAction_ordinaryLine_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/91f94613-df71-5ab5-8a93-373fd365af61
-- title:
--   Galois-stable Hecke line and dual quotient mod r in e H¹
-- statement:
--   Let $\mathcal O$ be a characteristic-zero discrete valuation ring and $k$ an $\mathcal O$-algebra which is a field of characteristic $p$, with $\mathcal O\to k$ surjective, $p$ an odd prime. Let $M'\neq 0$ satisfy $p\mid M'$, $p^2\nmid M'$, let $H'\le(\mathbb Z/M')^\times$ contain every unit whose image in $(\mathbb Z/(M'/p))^\times$ is $1$, and let $d\in(\mathbb Z/M')^\times$ have image in $\mathbb Z/(M'/p)$ equal to the class of $p$, with the image of $d$ or of $-d$ lying in the image of $H'$ in $(\mathbb Z/(M'/p))^\times$. Let $S$ be a finite set of naturals, and let $\mathbb T$ be a commutative $\mathcal O$-algebra acting on $H^1=\mathrm{Hom}(\Gamma_{H'}(M')^{\mathrm{ab}},\mathcal O)$ compatibly with $\mathcal O$, faithfully, through elements $\mathrm{op}(g)$ realising the operator family indexed by the generators $T_\ell$ ($\ell$ prime, $\ell\notin S$, $\ell\nmid M'$), $U_q$ ($q\mid M'$ prime) and diamonds $\langle d\rangle$, and generated over $\mathcal O$ by their range. Let $\bar\theta$ be a $k$-valued function on those generators. Let $S'$ be a complete orthogonal family of idempotents $e_i$ of $\mathbb T$ together with maximal ideals $\mathfrak m_i$ exhausting $\operatorname{Spec}^{\max}\mathbb T$ with $e_i\in\mathfrak m_j\iff i\neq j$, fix an index $i_0$, write $A=e_{i_0}\mathbb T e_{i_0}$ and $P=e_{i_0}H^1$, and let $\pi_k\colon A\to k$ be an $\mathcal O$-algebra map sending the corner of each $\mathrm{op}(g)$ to $\bar\theta(g)$, with $\bar\theta(U_p)\neq 0$. Let $\bar\rho$ be a two-dimensional residual representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $k$ factoring through a finite level, absolutely irreducible, with $\operatorname{tr}\bar\rho(\sigma)=\bar\theta(T_\ell)$ for every Frobenius element $\sigma$ at any valuation subring of $\overline{\mathbb Q}$ over a prime $\ell\notin S$ with $\ell\nmid M'$. Let $P\!l$ be a valuation subring of $\overline{\mathbb Q}$ over $p$ and $r\neq 0$ an element of the maximal ideal of $\mathcal O$. Then there are a map $\rho$ from the Galois group to $\mathrm{End}_{\mathcal O}(P)$, an $A$-submodule $E\subseteq P$, an element $x\in P$, functions $\psi_E,\psi_0$ from the Galois group to $A$ and an $\mathcal O$-linear $\Phi\colon P\to\mathrm{Hom}_{\mathcal O}(A,\mathcal O/r)$ such that: $\rho$ is a unital, multiplicative and $A$-semilinear action modulo $rP$ (each identity holding up to an element of $rP$); $x\in E$, $rP\subseteq E$, every element of $E$ is $a\cdot x$ modulo $rP$ for some $a\in A$, and $a\cdot x\in rP$ exactly when $a\in rA$; $\Phi$ is surjective with kernel $E$ and satisfies $\Phi(a\cdot v)(t)=\Phi(v)(at)$; for $\sigma$ in the decomposition subgroup at $P\!l$ one has $\rho(\sigma)x\equiv\psi_E(\sigma)\cdot x$ modulo $rP$ and $\rho(\sigma)v\equiv\psi_0(\sigma)\cdot v$ modulo $E$ for all $v$, while $\rho(\sigma)v\equiv v$ modulo $E$ for $\sigma$ in the image of the inertia subgroup; and for $\sigma$ in the decomposition subgroup the characteristic polynomial of $\bar\rho(\sigma)$ equals $(X-\pi_k(\psi_E(\sigma)))(X-\pi_k(\psi_0(\sigma)))$.
--
--   This is the ordinary filtration at $p$ on the localised weight-two cohomology of $\Gamma_{H'}(M')$, in the form used by Wiles: modulo $r$ the corner module $e\,H^1$ carries a Galois action with a free rank-one Hecke line spanned by $x$, on which the decomposition group acts by the unramified character $\psi_E$, and with quotient the $\mathcal O/r$-dual of the corner ring, on which it acts by $\psi_0$; the two characters reduce to the diagonal of $\bar\rho$ on a decomposition group. The extra hypothesis over the unsuffixed version is that the class of $p$ lies in $\pm$ the image of $H'$ at level $M'/p$. It feeds the construction of a complementary splitting and the identification of the line and the quotient with the corner ring and its dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_galoisAction_ordinaryLine_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_galoisAction_ordinaryLine_mod_cornerSubmodule_H1_of_ordinary_of_level_trivial_at_p_of_mem_infSubgroup
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
      (x : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))
      (ψE ψ0 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (Φ : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)) →ₗ[𝒪]
        (S'.CornerRing i₀ →ₗ[𝒪] 𝒪 ⧸ Ideal.span {r})),

      (∀ v, ∃ w, ρ 1 v = v + r • w) ∧
      (∀ σ τ v, ∃ w, ρ (σ * τ) v = ρ σ (ρ τ v) + r • w) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : S'.CornerRing i₀) v,
        ∃ w, ρ σ (a • v) = a • ρ σ v + r • w) ∧

      x ∈ E ∧ (∀ w, r • w ∈ E) ∧
      (∀ v ∈ E, ∃ (a : S'.CornerRing i₀)
        (w : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀))),
        v = a • x + r • w) ∧
      (∀ a : S'.CornerRing i₀,
        (∃ w : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
            a • x = r • w) ↔
          ∃ b : S'.CornerRing i₀, a = algebraMap 𝒪 (S'.CornerRing i₀) r * b) ∧

      Function.Surjective Φ ∧ (∀ v, Φ v = 0 ↔ v ∈ E) ∧
      (∀ (a : S'.CornerRing i₀) (v : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))
        (t : S'.CornerRing i₀), Φ (a • v) t = Φ v (a * t)) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∃ w, ρ σ x = ψE σ • x + r • w) ∧
      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∀ v, ρ σ v - ψ0 σ • v ∈ E) ∧
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ v, ρ σ v - v ∈ E) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ,
        LinearMap.charpoly (ρbar.ρ σ) =
          (Polynomial.X - Polynomial.C (πk (ψE σ))) * (Polynomial.X - Polynomial.C (πk (ψ0 σ)))) := by sorry
