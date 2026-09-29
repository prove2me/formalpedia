-- Prove2me | Theorems.Thm_CohCarrier_exists_galoisAction_trace_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
-- name    : CohCarrier.exists_galoisAction_trace_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/81c628a8-7f08-5ff3-97b7-e40dc3845eda
-- title:
--   Ordinary filtration, trace and determinant mod r on a non-Eisenstein corner
-- statement:
--   Let $\mathcal O$ be a characteristic-zero discrete valuation ring, $k$ a field that is an $\mathcal O$-algebra with surjective structure map, $p$ an odd prime with $\operatorname{char} k = p$, and $M'$ a positive integer with $p \mid M'$, $p^2 \nmid M'$. Let $H' \le (\mathbb Z/M')^\times$ contain every unit whose image in $(\mathbb Z/(M'/p))^\times$ is $1$, and let $d \in (\mathbb Z/M')^\times$ have image in $\mathbb Z/(M'/p)$ equal to the class of $p$, with the image of $d$ or of $-d$ in $(\mathbb Z/(M'/p))^\times$ lying in [`ModularCurve.infSubgroup p M' H' hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H'$ under reduction. Let $S$ be a finite set of naturals. Write $P_0 =$ [`CohCarrier.H1 M' H' 𝒪`](def/CohCarrier_Level.html#L162), the group of additive homomorphisms from $\Gamma_{H'}(M')$ (the preimage of $H'$ in $\Gamma_0(M') \le \mathrm{SL}_2(\mathbb Z)$), written additively, to $\mathcal O$. Let $\mathbb T$ be a commutative $\mathcal O$-algebra acting on $P_0$ compatibly with the $\mathcal O$-action and faithfully (any $t$ annihilating $P_0$ is $0$), let $\mathrm{op}$ send each generator symbol in [`CohCarrier.Gen M' S`](def/CohCarrier_Inst.html#L13) — the symbols $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M'$), $U_q$ ($q$ prime, $q \mid M'$) and $\langle d \rangle$ — to an element of $\mathbb T$ acting as the corresponding operator [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91), and assume these elements generate $\mathbb T$ as an $\mathcal O$-algebra. Let $\bar\theta$ be a $k$-valued function on the generator symbols. Let $S'$ be an idempotent splitting of $\mathbb T$: complete orthogonal idempotents $e_i$ together with maximal ideals $\mathfrak m_i$ exhausting all maximal ideals and satisfying $e_i \in \mathfrak m_j \iff i \ne j$. Fix an index $i_0$, put $A = e_{i_0}\mathbb T e_{i_0}$ and $P = e_{i_0} P_0$, and let $\pi_k \colon A \to k$ be an $\mathcal O$-algebra map carrying the corner of $\mathrm{op}(g)$ to $\bar\theta(g)$ for every generator $g$. Assume $\bar\theta(U_p) \ne 0$, and that for some prime $\ell \notin S$ with $\ell \nmid M'$ and $\ell \equiv 1 \pmod{M'}$ one has $\bar\theta(T_\ell) \ne \ell + 1$ in $k$. Let $P_\ell$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit in it, and let $r$ be a nonzero element of the maximal ideal of $\mathcal O$. Then there exist a map $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathcal O$-endomorphisms of $P$, maps $\mathrm{tr}, \mathrm{dt}, \psi_E, \psi_0$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $A$, a subfield $L$ of $\overline{\mathbb Q}$, an $A$-submodule $E \subseteq P$ and an $\mathcal O$-linear $\Phi \colon P \to \mathrm{Hom}_{\mathcal O}(A, \mathcal O/(r))$ such that, all congruences being modulo $r$ times an element of the relevant module or ring: $\rho(1) = \mathrm{id}$, $\rho(\sigma\tau) = \rho(\sigma)\rho(\tau)$ and $\rho(\sigma)(av) = a\,\rho(\sigma)v$ for $a \in A$; $L$ is finite over $\mathbb Q$ and every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma) = \mathrm{id}$ and $\mathrm{tr}(\sigma\tau) = \mathrm{tr}(\tau)$ for all $\tau$; $\mathrm{tr}(\sigma\tau\sigma^{-1}) = \mathrm{tr}(\tau)$, $\rho(\sigma)^2 + \mathrm{dt}(\sigma) = \mathrm{tr}(\sigma)\rho(\sigma)$ on $P$, and $\mathrm{tr}(\sigma)^2 = \mathrm{tr}(\sigma^2) + 2\,\mathrm{dt}(\sigma)$; for every prime $\ell \notin S$ with $\ell \nmid M'$, every valuation subring of $\overline{\mathbb Q}$ in which $\ell$ is a nonunit and every $\sigma$ that is a Frobenius at $\ell$ for it, $\mathrm{tr}(\sigma)$ agrees with the image of $\mathrm{op}(T_\ell)$ in $A$; $rP \subseteq E$; $\Phi$ is surjective with kernel exactly $E$ and satisfies $\Phi(av)(b) = \Phi(v)(ab)$; for $\sigma$ in the decomposition subgroup of $P_\ell$, $\rho(\sigma)$ acts on $E$ by the scalar $\psi_E(\sigma)$ and $\rho(\sigma)v - \psi_0(\sigma)v \in E$ for all $v \in P$, while for $\sigma$ in the inertia subgroup sitting inside that decomposition subgroup one has $\rho(\sigma)v - v \in E$; and on the decomposition subgroup $\mathrm{tr}(\sigma) = \psi_E(\sigma) + \psi_0(\sigma)$, $\mathrm{dt}(\sigma) = \psi_E(\sigma)\psi_0(\sigma)$.
--
--   This constructs, modulo a nonzero element $r$ of the maximal ideal of $\mathcal O$, the two-dimensional Galois action on an ordinary non-Eisenstein corner $e\,H^1(\Gamma_{H'}(M'),\mathcal O)$ together with its ordinary filtration $E$, the unramified-at-$p$ character $\psi_0$ on the quotient, the trace and determinant functions, and the duality identification of $P/E$ with $\mathrm{Hom}_{\mathcal O}(A,\mathcal O/(r))$, in the case where $p$ exactly divides the level and the class of $p$ modulo $M'/p$ lies in $\pm H'$. It is the variant of the corresponding statement without the condition on the class of $p$, and it is used in turn in the version of the construction for levels with trivial structure at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_galoisAction_trace_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_galoisAction_trace_ordinaryFiltration_quotient_dual_mod_cornerSubmodule_H1_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
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
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'), ℓ ≡ 1 [MOD M'] ∧
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ≠ (ℓ : k) + 1)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (r : 𝒪) (hr : r ∈ IsLocalRing.maximalIdeal 𝒪) (hr0 : r ≠ 0) :
    ∃ (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
          (↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)) →ₗ[𝒪]
            ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀))))
      (tr dt : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (L : IntermediateField ℚ (AlgebraicClosure ℚ))
      (E : Submodule (S'.CornerRing i₀)
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))
      (ψE ψ0 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (Φ : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)) →ₗ[𝒪]
        (S'.CornerRing i₀ →ₗ[𝒪] 𝒪 ⧸ Ideal.span {r})),

      (∀ v, ∃ w, ρ 1 v = v + r • w) ∧
      (∀ σ τ v, ∃ w, ρ (σ * τ) v = ρ σ (ρ τ v) + r • w) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : S'.CornerRing i₀) v,
        ∃ w, ρ σ (a • v) = a • ρ σ v + r • w) ∧

      FiniteDimensional ℚ L ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        (∀ v, ∃ w, ρ σ v = v + r • w) ∧ (∀ τ, ∃ b, tr (σ * τ) = tr τ + r • b)) ∧

      (∀ σ τ, ∃ b, tr (σ * τ * σ⁻¹) = tr τ + r • b) ∧
      (∀ σ v, ∃ w, ρ σ (ρ σ v) + dt σ • v = tr σ • ρ σ v + r • w) ∧
      (∀ σ, ∃ b, tr σ * tr σ = tr (σ * σ) + 2 * dt σ + r • b) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            ∃ b, tr σ = S'.toCornerRing i₀ (op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) + r • b) ∧

      (∀ w, r • w ∈ E) ∧

      Function.Surjective Φ ∧ (∀ v, Φ v = 0 ↔ v ∈ E) ∧
      (∀ (a : S'.CornerRing i₀) (v : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))
        (b : S'.CornerRing i₀), Φ (a • v) b = Φ v (a * b)) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∀ v ∈ E, ∃ w, ρ σ v = ψE σ • v + r • w) ∧
      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∀ v, ρ σ v - ψ0 σ • v ∈ E) ∧
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ v, ρ σ v - v ∈ E) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∃ b, tr σ = ψE σ + ψ0 σ + r • b) ∧
      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∃ b, dt σ = ψE σ * ψ0 σ + r • b) := by sorry
