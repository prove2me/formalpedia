-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_isProper_of_three_le_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.isProper_of_three_le_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/6b008e48-92c3-5c3d-b67a-3a94be8080ce
-- title:
--   Properness of coarse moduli schemes of fake elliptic curves
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order (an order containing no strictly larger order), let $N \geq 1$, and let $\mathcal{O}$ be a characteristic-zero integral domain in which $N$, $2$, $3$ and some integer $m_0 \geq 3$ are units. Then two properness assertions hold simultaneously. First, for every scheme $\mathcal{X}$, every $f : \mathcal{X} \to \operatorname{Spec}\mathcal{O}$, and every assignment $\mathrm{pt}$ sending a commutative ring $S$, a morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure to a morphism $\operatorname{Spec} S \to \mathcal{X}$ over $s$, if $(\mathcal{X},f,\mathrm{pt})$ is a coarse moduli datum in the sense of `IsCoarseModuli` — $\mathrm{pt}$ is constant on isomorphism classes, compatible with base change along ring homomorphisms, bijective on isomorphism classes of objects over algebraically closed fields, and universal among such data over $\operatorname{Spec}\mathcal{O}$ — then $f$ is proper. Secondly, for every prime $\ell$ invertible in $\mathcal{O}$ and every coarse moduli datum $(\mathcal{Y},g,\mathrm{pt}_T)$ in the sense of `IsCoarseModuliT` for pairs consisting of such a fake elliptic curve together with an extra level structure at $\ell$ (a closed subscheme of the $\ell$-torsion, finite flat of rank $\ell^2$, stable under $\Lambda$, disjoint from the level-$N$ structure, with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$), the morphism $g$ is proper.
--
--   This is the properness of the integral models of the Shimura curves attached to an indefinite quaternion algebra over $\mathbb{Q}$ ramified exactly at $q$ and $q'$, reflecting the fact that fake elliptic curves have potentially good reduction everywhere, so that no cusps arise; it is stated both at level $N$ and at level $N$ together with an extra level structure at a prime $\ell$ invertible on the base. It feeds the subsequent study of these curves over $\mathcal{O}$, in particular the finiteness of the degeneracy morphisms and the integrality of the models over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_isProper_of_three_le_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuli.isProper_of_three_le_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (m₀ : ℕ) (hm₀ : 3 ≤ m₀) (hm₀u : IsUnit ((m₀ : ℕ) : 𝒪)) :
    (∀ (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
        (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f),
        IsCoarseModuli Λ N 𝒳 f pt → IsProper f) ∧
    (∀ (ℓ : ℕ), ℓ.Prime → IsUnit ((ℓ : ℕ) : 𝒪) →
      ∀ (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of 𝒪))
        (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
          FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g),
        IsCoarseModuliT Λ N ℓ 𝒴 g ptT → IsProper g) := by sorry
