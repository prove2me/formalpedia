-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_subgroup_mem_iff_forall_mul_mem
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.exists_subgroup_mem_iff_forall_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7853e1e2-6415-513c-acac-657929c8d410
-- title:
--   Stabiliser of a left ideal under a level-twisting labelling
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project predicate `IsOrder`: $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is all of $\mathbb{H}[\mathbb{Q},a,b]$, and it is finitely generated. Fix naturals $N$ and $m$ with $m\neq 0$, a commutative ring $B$, a scheme $M$ with a morphism $\pi_M : M \to \operatorname{Spec} B$, and a rule $\mathrm{ptF}$ which to every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every pair consisting of a fake elliptic curve over $S$ for $(\Lambda,N)$ together with a full level-$m$ structure on it assigns a point of $M$ over $s$, i.e. a morphism $\operatorname{Spec} S \to M$ whose composite with $\pi_M$ is $s$. Fix a group $G$, a homomorphism $\rho : G \to \operatorname{Aut} M$ and a map $\chi : G \to \Lambda$ such that `IsLevelTwistAction` holds: each $\rho(g)$ is a morphism over $\operatorname{Spec} B$; whenever $u'$ is a $\chi(g)$-twist of $u$ one has $\mathrm{ptF}(S,s,u') = \mathrm{ptF}(S,s,u)$ followed by $\rho(g)$; $\chi(1)\equiv 1$ and $\chi(gg')\equiv\chi(g)\chi(g')$ modulo $m\Lambda$; every $c\in\Lambda$ admitting a two-sided inverse modulo $m\Lambda$ is congruent to some $\chi(g)$ modulo $m\Lambda$; and $\chi(g)\equiv\chi(g')$ modulo $m\Lambda$ forces $g=g'$. Let finally $L_0$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ contained in $\Lambda$, let $\ell$ be a natural number dividing $m$ with $\ell x \in L_0$ for all $x\in\Lambda$, and assume $y L_0 \subseteq L_0$ for every $y\in\Lambda$. Then there is a subgroup $H \le G$ whose members are exactly the $g$ with $x\chi(g)\in L_0$ for all $x\in L_0$.
--
--   The subgroup produced here is the stabiliser in $G$ of a left $\Lambda$-stable lattice $L_0$ under right multiplication by the labels $\chi(g)$; passing to its quotient or fixed locus is what cuts the full-level quaternionic moduli problem down to a level structure of the desired type. It is used in the construction of coarse moduli schemes for the quaternionic problem and in the proofs of their integrality and properness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_subgroup_mem_iff_forall_mul_mem.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsLevelTwistAction.exists_subgroup_mem_iff_forall_mul_mem
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (N m : ℕ) [NeZero m] {B : Type} [CommRing B]
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) {ℓ : ℕ} (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀) (hℓm : ℓ ∣ m)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀) :
    ∃ H : Subgroup G, ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀ := by sorry
