-- Prove2me | Theorems.Thm_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible
-- name    : CohCarrier.exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/9c5e3af7-b8b2-53cb-8942-c2bffffbbb71
-- title:
--   Dual Galois module for localised H¹(Γ_H(M)) with Eichler–Shimura relation
-- statement:
--   Let $\mathcal O$ be a characteristic-zero discrete valuation domain, $k$ an $\mathcal O$-algebra which is a field with $\mathcal O \to k$ surjective, $p \neq 2$ a prime with $\mathrm{char}\,k = p$, $M' \geq 1$, $H' \leq (\mathbb Z/M')^{\times}$ and $S$ a finite set of naturals. Let $\mathbb T$ be a commutative $\mathcal O$-algebra acting on $H^1 = \mathrm{Hom}(\Gamma_{H'}(M')^{\mathrm{ab}}, \mathcal O)$ (additive maps from $\mathrm{Additive}\,\Gamma_{H'}(M')$ to $\mathcal O$) compatibly with the $\mathcal O$-action, faithfully (only $t=0$ kills all of $H^1$), and suppose given $\mathrm{op} : \mathrm{Gen}\,M'\,S \to \mathbb T$ realising the transfer-defined operators $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M'$), $U_q$ ($q \mid M'$ prime) and $\langle d\rangle$ on $H^1$, with $\mathcal O$-adjoin of its range all of $\mathbb T$. Let $S'$ be an idempotent splitting of $\mathbb T$ (complete orthogonal idempotents $e_i$ matched bijectively with the maximal ideals $\mathfrak m_i$, all maximal ideals occurring, $e_i \in \mathfrak m_j$ iff $i \neq j$), $i_0$ an index, and $\pi_k$ an $\mathcal O$-algebra map from the corner ring $e_{i_0}\mathbb T e_{i_0}$ to $k$ whose values $\pi_k(e_{i_0}\,\mathrm{op}(g)\,e_{i_0}) = \bar\theta(g)$ define $\bar\theta : \mathrm{Gen}\,M'\,S \to k$. Let $\bar\rho$ be a residual Galois representation over $k$ (a two-dimensional $k$-space $V$ with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k V$ factoring through a finite level), absolutely irreducible (irreducible after base change to $\bar k$), and assume $\mathrm{tr}\,\bar\rho(\sigma) = \bar\theta(T_\ell)$ for every prime $\ell \notin S$ with $\ell \nmid M'$, every valuation subring $A$ of $\bar{\mathbb Q}$ with $\ell$ a nonunit of $A$, and every $\sigma$ in the decomposition subgroup of $A$ acting as $x \mapsto x^{\ell}$ on the residue field. Then there exist a finite-dimensional $k$-vector space $W$, a monoid homomorphism $\sigma_W$ from $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k W$, and an additive map $\Psi : H^1 \to W^{*}$ such that: the kernel of $\sigma_W$ is open; $\Psi(t\cdot v) = \pi_k(e_{i_0} t e_{i_0})\,\Psi(v)$ for all $t \in \mathbb T$; $\Psi(\iota v) = \Psi(v) \circ \sigma_W(c)$, where $\iota$ is precomposition on $H^1$ with the involution $\gamma \mapsto J\gamma J^{-1}$ of $\Gamma_{H'}(M')$ and $c$ is complex conjugation; $\Psi$ is surjective; for $m$ in the corner submodule $e_{i_0}\cdot H^1$ one has $\Psi(m) = 0$ iff $m$ lies in $\mathfrak m\cdot(e_{i_0}\cdot H^1)$, $\mathfrak m$ the maximal ideal of the local corner ring; and for every prime $\ell \notin S$ with $\ell \nmid M'$, $\ell \neq p$, every $A$ over $\ell$ and every Frobenius $\sigma$ at $\ell$ for $A$, $\sigma_W(\sigma)^2 - \bar\theta(T_\ell)\,\sigma_W(\sigma) + \ell\,\bar\theta(\langle \ell\rangle) = 0$.
--
--   This is the Eichler–Shimura comparison at a non-Eisenstein maximal ideal: the fibre at $\mathfrak m$ of the localised cohomology of $\Gamma_{H'}(M')$ is realised as the $k$-dual of a finite Galois module on which the congruence relation $\sigma^2 - T_\ell\sigma + \ell\langle\ell\rangle = 0$ holds and on which the involution of $H^1$ corresponds to complex conjugation. It is used to identify the corner submodule of $H^1$ modulo $\mathfrak m$ with an eigenspace of such a Galois module, en route to attaching Galois representations to Hecke eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ) (S : Finset ℕ)
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
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
      (σW : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (W →ₗ[k] W))
      (Ψ : CohCarrier.H1 M' H' 𝒪 →+ Module.Dual k W),
      IsOpen ((σW.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∧
      (∀ (t : 𝕋) (v : CohCarrier.H1 M' H' 𝒪), Ψ (t • v) = πk (S'.toCornerRing i₀ t) • Ψ v) ∧
      (∀ v : CohCarrier.H1 M' H' 𝒪,
        Ψ (CohCarrier.charInvolution M' H' 𝒪 𝒪 v) = (Ψ v) ∘ₗ σW complexConjugation) ∧
      Function.Surjective Ψ ∧
      (∀ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
        Ψ (m : CohCarrier.H1 M' H' 𝒪) = 0 ↔
          m ∈ IsLocalRing.maximalIdeal (S'.CornerRing i₀) •
            (⊤ : Submodule (S'.CornerRing i₀)
              ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            σW σ * σW σ - θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) • σW σ +
              ((ℓ : k) * θbar (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) • 1 = 0) := by sorry
