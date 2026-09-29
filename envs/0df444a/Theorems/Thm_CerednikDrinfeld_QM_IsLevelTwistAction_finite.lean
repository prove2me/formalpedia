-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_finite
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/95c1d6af-f85e-55e3-b2bf-1ce39ddd5be4
-- title:
--   Finiteness of a group acting by level twists
-- statement:
--   Fix natural numbers $r,\bar r,N$ with $r,\bar r$ prime, $\bar r\neq r$, $N$ nonzero and squarefree and divisible by neither $r$ nor $\bar r$; a domain $\mathcal O$ of characteristic zero which is a discrete valuation ring, complete for the adic topology of a prime element $\pi$, with residue ring of cardinality $r$ and $(r)=(\pi)$; rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0<a$ or $0<b$ and, for a finite place $v$ of $\mathbb Q$, the completed algebra is a division algebra exactly when $v$ lies over $r$ or $\bar r$; and a maximal order $\Lambda$ (an order containing no larger order). Fix $n\ge 3$ coprime to $N$ and divisible by neither $r$ nor $\bar r$, a scheme $M$ with a morphism $f_M$ to $\operatorname{Spec}\mathcal O$ and a point-assignment $\mathrm{ptF}$ making $(M,f_M,\mathrm{ptF})$ a fine moduli space for fake elliptic curves of level $N$ with full level-$n$ structure, with $f_M$ separated and every finite subset of $M$ contained in an affine open. Let $G$ be a group with a homomorphism $\rho$ to $\operatorname{Aut} M$ and a map $\chi\colon G\to\Lambda$ satisfying `IsLevelTwistAction`: each $\rho(g)$ lies over the base, twisting a full-level structure by $\chi(g)$ transports its moduli point along $\rho(g)$, and $\chi$ is multiplicative, normalised, surjective and injective modulo $n\Lambda$. Finally let $\mathcal Y_\ell$, $g_\ell$, $\mathrm{ptT}_\ell$ be coarse moduli data for extra level $\ell$ at each prime $\ell\neq r,\bar r$. Then $G$ is finite.
--
--   The finiteness statement needed to form quotients of the fine moduli scheme by a group acting through level twists; it is used in the construction of coarse moduli spaces in the Hecke tower, being cited by [`CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient) and `CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli`-style quotient presentations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_finite.lean

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

theorem CerednikDrinfeld.QM.IsLevelTwistAction.finite

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
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ)) :
    Finite G := by sorry
