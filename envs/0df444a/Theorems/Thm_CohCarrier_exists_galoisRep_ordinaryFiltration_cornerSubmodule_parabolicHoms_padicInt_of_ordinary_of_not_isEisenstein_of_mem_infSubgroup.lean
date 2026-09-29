-- Prove2me | Theorems.Thm_CohCarrier_exists_galoisRep_ordinaryFiltration_cornerSubmodule_parabolicHoms_padicInt_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
-- name    : CohCarrier.exists_galoisRep_ordinaryFiltration_cornerSubmodule_parabolicHoms_padicInt_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/906ef3bc-244d-58de-a077-ff3a4301b732
-- title:
--   Ordinary Galois representation on a non-Eisenstein corner of parabolic cohomology
-- statement:
--   Let $p$ be an odd prime, let $M \ge 1$ with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb Z/M)^\times$ contain every unit whose image in $(\mathbb Z/(M/p))^\times$ is $1$. Assume given $d \in (\mathbb Z/M)^\times$ whose image in $\mathbb Z/(M/p)$ equals $p$ and such that this image, or its negative, lies in [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ in $(\mathbb Z/(M/p))^\times$. Let $S$ be a finite set of naturals and write $W$ for [`ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p]`](def/ModularCurve_PeriodMap.html#L62), the submodule of additive homomorphisms $\operatorname{Hom}(\Gamma_H(M), \mathbb Z_p)$ cut out by `IsParabolicHom`, where $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb Z)$ is the preimage of $H$ in $\Gamma_0(M)$. Let $\mathbb T$ be a commutative $\mathbb Z_p$-algebra acting on $W$ compatibly with the $\mathbb Z_p$-action and faithfully (every $t$ annihilating $W$ is $0$), and let $\mathrm{op} \colon$ [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) $\to \mathbb T$ be a map whose values act on $W$ through [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91), i.e. by the transfer-type Hecke operators attached to the generators $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M$), $U_q$ ($q$ prime, $q \mid M$) and the diamond operators $\langle d \rangle$ on $\operatorname{Hom}(\Gamma_H(M), \mathbb Z_p)$, and whose range generates $\mathbb T$ as a $\mathbb Z_p$-algebra. Let $S'$ be an idempotent splitting of $\mathbb T$ (finitely many complete orthogonal idempotents $e_i$ together with maximal ideals $\mathfrak m_i$ exhausting the maximal ideals of $\mathbb T$, with $e_i \in \mathfrak m_j$ exactly for $i \ne j$), fix an index $i_0$, put $A = e_{i_0} \mathbb T e_{i_0}$ and $P = e_{i_0} \cdot W$, and let $\pi \colon A \to k$ be a ring homomorphism into a field $k$ of characteristic $p$, with $\bar\theta(g) = \pi(e_{i_0}\,\mathrm{op}(g)\,e_{i_0})$. Assume ordinarity, $\bar\theta(U_p) \ne 0$, and non-Eisensteinness: there is a prime $\ell \notin S$ with $\ell \nmid M$, $\ell \equiv 1 \pmod M$ and $\bar\theta(T_\ell) \ne \ell + 1$. Finally let $Pl$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ in its nonunits. Then there exist a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to the $A$-linear endomorphisms of $P$, functions $\mathrm{tr}, \mathrm{dt}, \psi_E, \psi_0$ from the Galois group to $A$, finite-dimensional intermediate fields $L_n$ of $\overline{\mathbb Q}/\mathbb Q$, an $A$-submodule $E \subseteq P$, and a $\mathbb Z_p$-linear map $\Psi \colon P \to \operatorname{Hom}_{\mathbb Z_p}(A, \mathbb Z_p)$ such that: every $\sigma$ fixing $L_n$ pointwise satisfies $\rho(\sigma)v \in v + p^n P$ for all $v$ and $\mathrm{tr}(\sigma\tau) \equiv \mathrm{tr}(\tau)$, $\mathrm{dt}(\sigma\tau) \equiv \mathrm{dt}(\tau)$ modulo $p^n A$ for all $\tau$; $\mathrm{tr}(1) = 2$, $\mathrm{dt}(1) = 1$, both $\mathrm{tr}$ and $\mathrm{dt}$ are conjugation-invariant, $\mathrm{dt}$ is multiplicative, $\mathrm{tr}(\sigma)^2 = \mathrm{tr}(\sigma^2) + 2\,\mathrm{dt}(\sigma)$, and $\rho(\sigma)^2 - \mathrm{tr}(\sigma)\rho(\sigma) + \mathrm{dt}(\sigma) = 0$ on $P$; for every prime $\ell \notin S$ with $\ell \nmid M$, every valuation subring of $\overline{\mathbb Q}$ with $\ell$ in its nonunits and every $\sigma$ that is a Frobenius at $\ell$ for it (lying in the decomposition subgroup and acting as $x \mapsto x^\ell$ on the residue field), $\mathrm{tr}(\sigma) = e_{i_0}\,\mathrm{op}(T_\ell)\,e_{i_0}$; $\Psi$ is surjective, its zero locus is exactly $E$, and $\Psi(a \cdot v)(b) = \Psi(v)(ab)$; and, on the decomposition subgroup of $Pl$ over $\mathbb Q$, $\rho(\sigma)$ acts on $E$ as multiplication by $\psi_E(\sigma)$, $\rho(\sigma)v - \psi_0(\sigma)v \in E$ for all $v \in P$, $\mathrm{tr}(\sigma) = \psi_E(\sigma) + \psi_0(\sigma)$ and $\mathrm{dt}(\sigma) = \psi_E(\sigma)\psi_0(\sigma)$, while every $\sigma$ in the image of the inertia subgroup satisfies $\rho(\sigma)v - v \in E$.
--
--   This is the construction of the two-dimensional $p$-adic representation carried by a non-Eisenstein, ordinary local factor of the parabolic cohomology of $\Gamma_H(M)$, presented through a trace and determinant function together with the ordinary filtration $E \subseteq P$ at $p$ and the duality $\Psi$, in the style of Wiles' Chapter 2. It is used by the variant of the same statement in which the representation is given by explicit $2 \times 2$ matrices over the corner ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_galoisRep_ordinaryFiltration_cornerSubmodule_parabolicHoms_padicInt_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CohCarrier.exists_galoisRep_ordinaryFiltration_cornerSubmodule_parabolicHoms_padicInt_of_ordinary_of_not_isEisenstein_of_mem_infSubgroup
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    (S : Finset ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋]
    [Module 𝕋 ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])]
    [IsScalarTower ℤ_[p] 𝕋 ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])]
    (hfaith : ∀ t : 𝕋,
      (∀ v : ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p]), t • v = 0) → t = 0)
    (op : CohCarrier.Gen M ↑S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M ↑S)
      (v : ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])),
      ((op g • v : ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])) :
          CohCarrier.H1 M H ℤ_[p]) =
        CohCarrier.opFamily M H ↑S ℤ_[p] g (v : CohCarrier.H1 M H ℤ_[p]))
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    {k : Type} [Field k] [CharP k p] (πk : S'.CornerRing i₀ →+* k) (θbar : CohCarrier.Gen M ↑S → k)
    (hπk : ∀ g : CohCarrier.Gen M ↑S, πk (S'.toCornerRing i₀ (op g)) = θbar g)
    (hord : θbar (CohCarrier.Gen.U p Fact.out hpM) ≠ 0)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≡ 1 [MOD M] ∧
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ≠ (ℓ : k) + 1)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p) :
    ∃ (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
          Module.End (S'.CornerRing i₀)
            ↥(IharaLemma.cornerSubmodule
              (M := ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])) (S'.e i₀)))
      (tr dt ψE ψ0 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ))
      (E : Submodule (S'.CornerRing i₀)
        ↥(IharaLemma.cornerSubmodule
          (M := ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])) (S'.e i₀)))
      (Ψ : ↥(IharaLemma.cornerSubmodule
          (M := ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])) (S'.e i₀)) →ₗ[ℤ_[p]]
        (S'.CornerRing i₀ →ₗ[ℤ_[p]] ℤ_[p])),

      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ v, ∃ w, ρ σ v = v + ((p : ℤ_[p]) ^ n) • w) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, tr (σ * τ) = tr τ + (p : S'.CornerRing i₀) ^ n * b) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, dt (σ * τ) = dt τ + (p : S'.CornerRing i₀) ^ n * b)) ∧

      tr 1 = 2 ∧ dt 1 = 1 ∧
      (∀ σ τ, tr (σ * τ * σ⁻¹) = tr τ) ∧ (∀ σ τ, dt (σ * τ * σ⁻¹) = dt τ) ∧
      (∀ σ τ, dt (σ * τ) = dt σ * dt τ) ∧
      (∀ σ, tr σ * tr σ = tr (σ * σ) + 2 * dt σ) ∧
      (∀ σ v, ρ σ (ρ σ v) - tr σ • ρ σ v + dt σ • v = 0) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            tr σ = S'.toCornerRing i₀ (op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM))) ∧

      Function.Surjective Ψ ∧ (∀ v, Ψ v = 0 ↔ v ∈ E) ∧
      (∀ (a : S'.CornerRing i₀)
        (v : ↥(IharaLemma.cornerSubmodule
          (M := ↥(ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p])) (S'.e i₀)))
        (b : S'.CornerRing i₀), Ψ (a • v) b = Ψ v (a * b)) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∀ v ∈ E, ρ σ v = ψE σ • v) ∧
      (∀ σ ∈ Pl.decompositionSubgroup ℚ, ∀ v, ρ σ v - ψ0 σ • v ∈ E) ∧
      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ v, ρ σ v - v ∈ E) ∧

      (∀ σ ∈ Pl.decompositionSubgroup ℚ, tr σ = ψE σ + ψ0 σ) ∧
      (∀ σ ∈ Pl.decompositionSubgroup ℚ, dt σ = ψE σ * ψ0 σ) := by sorry
