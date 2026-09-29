-- Prove2me | Theorems.Thm_CohCarrier_exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius
-- name    : CohCarrier.exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/615ea320-7a21-5afa-85b6-16b5dcdf6349
-- title:
--   Eichler–Shimura duality mod p for parabolic H¹ of Γ_H(M)
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain of characteristic zero, $k$ a field of characteristic $p$ ($p$ prime) which is an $\mathcal{O}$-algebra such that the structure map $\mathcal{O}\to k$ is surjective, let $M$ be a nonzero natural number, $H\le(\mathbb{Z}/M)^{\times}$ a subgroup, and $S$ a set of natural numbers. Write $\Gamma_H(M)=$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the elements of $\Gamma_0(M)$ whose associated unit under [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121) (the reduction mod $M$ of the lower-right entry) lies in $H$, and $\Lambda=$ [`CohCarrier.H1 M H 𝒪`](def/CohCarrier_Level.html#L162) for the $\mathcal{O}$-module of additive homomorphisms $\mathrm{Additive}(\Gamma_H(M))\to\mathcal{O}$, with $\Lambda_{\mathrm{par}}=$ [`ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪`](def/ModularCurve_PeriodMap.html#L62) its submodule cut out by the predicate `IsParabolicHom`. The assertion is the existence of a finite-dimensional $k$-vector space $V$, a monoid homomorphism $\sigma_V$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) to the $k$-linear endomorphisms of $V$, a family $t$ of $k$-linear endomorphisms of $V$ indexed by the generators [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (symbols $T_\ell$ for primes $\ell\notin S$ with $\ell\nmid M$, $U_q$ for primes $q\mid M$, and $\langle d\rangle$ for $d\in(\mathbb{Z}/M)^{\times}$), and an $\mathcal{O}$-linear map $\Phi\colon\Lambda\to\mathrm{Hom}_k(V,k)$, subject to: the kernel of $\sigma_V$ is open; each $t_g$ commutes with every $\sigma_V(\tau)$; for every generator $g$ and every $v\in\Lambda_{\mathrm{par}}$, $\Phi$ of [`CohCarrier.opFamily M H S 𝒪 g v`](def/CohCarrier_Inst.html#L91) equals $\Phi(v)\circ t_g$, where `opFamily` sends $T_\ell$ and $U_q$ to the transfer-theoretic Hecke operator [`CohCarrier.heckeTL`](def/CohCarrier_Inst.html#L23) and $\langle d\rangle$ to the diamond operator obtained from a chosen $\Gamma_0(M)$-lift of $d$; for $v\in\Lambda_{\mathrm{par}}$, $\Phi(\iota v)=\Phi(v)\circ\sigma_V(c)$, where $\iota=$ [`CohCarrier.charInvolution`](def/CohCarrier_CharInvolution.html#L43) is precomposition with the endomorphism of $\Gamma_H(M)$ induced by [`ModularCurve.Period.jConjSL`](def/ModularCurve_PeriodHomPair.html#L47) and $c=$ [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30) is the restriction to $\overline{\mathbb{Q}}$ of complex conjugation on $\mathbb{C}$; $\Phi(\Lambda_{\mathrm{par}})$ is all of $\mathrm{Hom}_k(V,k)$; for $v\in\Lambda_{\mathrm{par}}$, $\Phi(v)=0$ if and only if $v\in\mathfrak{m}_{\mathcal{O}}\Lambda_{\mathrm{par}}$; and finally, for every prime $\ell\notin S$ with $\ell\nmid M$ and $\ell\neq p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x\mapsto x^{\ell}$, one has $\sigma_V(\sigma)^2-t_{T_\ell}\,\sigma_V(\sigma)+\ell\cdot t_{\langle\ell\rangle}=0$, where $\langle\ell\rangle$ is the diamond symbol attached to the unit $\ell\bmod M$.
--
--   This is the mod $p$ Eichler–Shimura comparison in the form used later: the parabolic cohomology of $\Gamma_H(M)$ with $\mathcal{O}$-coefficients is put in perfect duality, after reduction modulo the maximal ideal, with a finite-dimensional $k$-linear Galois module on which the Hecke and diamond symbols act by Galois-commuting endomorphisms and on which Frobenius at $\ell$ satisfies the congruence relation $X^2-T_\ell X+\ell\langle\ell\rangle$. It is the input to [`CohCarrier.exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible`](thm.html#CohCarrier.exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible), and thus to the construction of the mod $p$ representation attached to a Hecke eigenclass.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (σV : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V →ₗ[k] V))
      (t : CohCarrier.Gen M S → (V →ₗ[k] V))
      (Φ : CohCarrier.H1 M H 𝒪 →ₗ[𝒪] Module.Dual k V),
      IsOpen ((σV.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∧
      (∀ (g : CohCarrier.Gen M S) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        t g * σV τ = σV τ * t g) ∧
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H 𝒪),
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪 →
          Φ (CohCarrier.opFamily M H S 𝒪 g v) = (Φ v) ∘ₗ t g) ∧
      (∀ v : CohCarrier.H1 M H 𝒪,
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪 →
          Φ (CohCarrier.charInvolution M H 𝒪 𝒪 v) = (Φ v) ∘ₗ σV complexConjugation) ∧
      (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪).map Φ = ⊤ ∧
      (∀ v : CohCarrier.H1 M H 𝒪,
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪 →
          (Φ v = 0 ↔ v ∈ IsLocalRing.maximalIdeal 𝒪 •
            ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            σV σ * σV σ - t (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) * σV σ +
              (ℓ : k) • t (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))) = 0) := by sorry
