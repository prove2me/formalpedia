-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_isCoarseModuli_pullback_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_isCoarseModuli_pullback_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/21909be7-ea53-5959-b9c1-fb32d66e40df
-- title:
--   Coarse moduli of fake elliptic curves under base change to a field
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0 < a$ or $0 < b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its completion at $v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (contains $1$, is multiplicatively closed, spans the algebra over $\mathbb{Q}$, finitely generated) and is maximal among orders, and let $N \geq 1$. Let $\mathcal{O}$ be a characteristic-zero domain in which $N$, $2$ and $3$ are units, and let $m_0 \geq 3$ be a natural number which is a unit in $\mathcal{O}$. Let $\pi_X : X \to \operatorname{Spec}\mathcal{O}$ be a morphism of schemes, separated and locally of finite type, and let $\mathrm{pt}$ assign to each commutative ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data (a commutative relative group law on a proper smooth $A \to \operatorname{Spec} S$ with connected two-dimensional fibres, an action of $\Lambda$ by group-law endomorphisms subject to the trace condition, together with the level structures of `FakeEllipticCurve`) a morphism $\operatorname{Spec} S \to X$ over $s$. Assume $\mathrm{pt}$ makes $X$ a coarse moduli scheme in the sense of `IsCoarseModuli`: $\mathrm{pt}$ is constant on isomorphism classes, compatible with pullback of curves along ring homomorphisms, bijective on isomorphism classes over algebraically closed fields, and universal among such point rules. Then for every field $k$ and every injective ring homomorphism $i : \mathcal{O} \to k$ there exists a point rule $\mathrm{pt}_k$ for which the second projection $X \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec} k \to \operatorname{Spec} k$ is again a coarse moduli scheme for fake elliptic curves with $\Lambda$-action and level-$N$ data.
--
--   This is the base-change stability of the coarse moduli scheme of fake elliptic curves (the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$) along an injection of the base domain into a field. It feeds the integrality, geometric reducedness and geometric connectedness statements about such coarse moduli schemes over algebraically closed and other fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_isCoarseModuli_pullback_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld NeronModelInfra
open CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_isCoarseModuli_pullback_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (m₀ : ℕ) (hm₀ : 3 ≤ m₀) (hm₀u : IsUnit ((m₀ : ℕ) : 𝒪))
    {X : Scheme.{0}} {πX : X ⟶ Spec (CommRingCat.of 𝒪)}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s πX}
    (hX : IsCoarseModuli Λ N X πX pt) (hsep : IsSeparated πX) (hlft : LocallyOfFiniteType πX)
    (k : Type) [Field k] (i : 𝒪 →+* k) (hi : Function.Injective i) :
    ∃ ptk : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k)),
        FakeEllipticCurve Λ N S → SchemeHomOver s (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom i))),
      IsCoarseModuli Λ N (Limits.pullback πX (Spec.map (CommRingCat.ofHom i)))
        (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom i))) ptk := by sorry
