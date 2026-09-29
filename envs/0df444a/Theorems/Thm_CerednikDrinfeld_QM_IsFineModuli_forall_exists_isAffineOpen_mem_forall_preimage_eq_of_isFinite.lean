-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite
-- name    : CerednikDrinfeld.QM.IsFineModuli.forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/25d3ed8d-94b8-55de-9040-db5e6eff7f8d
-- title:
--   A ρ_ℓ-invariant affine open around every point of M_ℓ
-- statement:
--   Fix distinct primes $r,\bar r$ neither dividing a squarefree $N\neq 0$, and a complete discrete valuation ring $\mathcal O$ of characteristic zero which is a domain, with irreducible element $\pi$, residue field of cardinality $r$, and $(r)=(\pi)$. Let $\mathbb H[\mathbb Q,a,b]$ satisfy `IsIndefiniteRamifiedExactlyAt a b r rbar` ($0<a$ or $0<b$, and the completion at a finite place $v$ of $\mathbb Q$ is a division algebra exactly when $v$ contains $r$ or $\bar r$), with $\Lambda$ a maximal order, and let $n\geq 3$ be coprime to $N$ and divisible by neither $r$ nor $\bar r$. Let $f_M : M \to \operatorname{Spec}\mathcal O$ together with $\mathrm{ptF}$ be a fine moduli scheme for fake elliptic curves of level $N$ with full level-$n$ structure (the point assignment is isomorphism-invariant, compatible with pullback along ring maps, and bijective on $S$-points), with $f_M$ separated and with the property that every finite subset of $M$ lies in an affine open. Let $G$ be a finite group acting on $M$ by $\rho$ with labels $\chi : G \to \Lambda$ forming a level-twist action (each $\rho(h)$ is over the base, twisting by $\chi(h)$ translates points by $\rho(h)$, and $\chi$ is multiplicative and bijective modulo $n$). Given further a coarse moduli tower $\mathcal Y_\ell \to \operatorname{Spec}\mathcal O$ with point assignments for extra level $\ell$ away from $r,\bar r$, a prime $\ell\neq r,\bar r$, a scheme $M_\ell$ over $\mathcal O$ with a finite morphism $\pi_\ell : M_\ell \to M$ compatible with the structure maps, and a homomorphism $\rho_\ell : G \to \operatorname{Aut} M_\ell$ over the base satisfying $\rho_\ell(h)$ followed by $\pi_\ell$ equals $\pi_\ell$ followed by $\rho(h)$, the conclusion is: every $x\in M_\ell$ lies in an affine open $U\subseteq M_\ell$ with $\rho_\ell(h)^{-1}U=U$ for all $h\in G$.
--
--   This is the admissibility condition for the finite group action of $G$ on $M_\ell$: each point has a $G$-stable affine open neighbourhood, which is what makes the quotient $M_\ell/G$ exist as a scheme. It is used in the construction of the fine moduli scheme with extra level $\ell$ as such a quotient presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_HeckeTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (hsep : IsSeparated fM) (hfin : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (ℓ : HeckeTower.AwayPrime r rbar)
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
    (πℓ : Mℓ ⟶ M) (hπℓf : πℓ ≫ fM = fMℓ) [IsFinite πℓ]
    (hG : Finite G)
    (ρℓ : G →* Aut Mℓ) (hρℓf : ∀ h : G, (ρℓ h).hom ≫ fMℓ = fMℓ)
    (hρℓπ : ∀ h : G, (ρℓ h).hom ≫ πℓ = πℓ ≫ (ρ h).hom) :
    ∀ x : Mℓ, ∃ U : Mℓ.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ h : G, (ρℓ h).hom ⁻¹ᵁ U = U := by sorry
