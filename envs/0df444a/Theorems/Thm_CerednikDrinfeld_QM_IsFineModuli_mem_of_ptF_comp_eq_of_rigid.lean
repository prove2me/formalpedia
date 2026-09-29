-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_mem_of_ptF_comp_eq_of_rigid
-- name    : CerednikDrinfeld.QM.IsFineModuli.mem_of_ptF_comp_eq_of_rigid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/05cc50af-e38b-5b10-90e1-efa6ea6c6ee8
-- title:
--   Stabiliser of a rigid fine moduli point lies in H
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, i.e. satisfies the predicate `IsOrder` and equals every order containing it; fix naturals $N,m$ and a commutative ring $\mathcal O$ in which the image of $m$ is a unit. Let $\pi_M:M\to\operatorname{Spec}\mathcal O$ be a scheme over $\mathcal O$ together with an assignment $\mathrm{ptF}$ sending each commutative ring $S$, each $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal O$ and each pair $u=(E,P)$ — $E$ a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data in the project's sense, $P$ a full level-$m$ structure on $E$ (an $S$-point of $E$ killed by $m$ whose $\Lambda$-translates exhaust the $m$-torsion at every geometric point, and whose annihilator in $\Lambda$ is $m\Lambda$) — to a morphism $\operatorname{Spec}S\to M$ composing with $\pi_M$ to $s$; assume $\mathrm{ptF}$ is a fine moduli datum, that is, constant on isomorphism classes, compatible with pullback along ring maps, surjective on $S$-points over any $s$, and injective up to isomorphism. Let $G$ be a finite group with $\rho:G\to\operatorname{Aut}M$ and $\chi:G\to\Lambda$ a level-twist action: each $\rho g$ lies over $\operatorname{Spec}\mathcal O$, twisting a pair by $\chi g$ moves its moduli point by $\rho g$, and $\chi$ is multiplicative, surjective and injective modulo $m\Lambda$ onto the classes invertible mod $m\Lambda$. Let $\ell$ be a prime dividing $m$, and $L_0\subseteq\Lambda$ a $\mathbb{Z}$-submodule containing $\ell\Lambda$, stable under left multiplication by $\Lambda$, of relative index $\ell^2$ in $\Lambda$, and let $H\le G$ be the subgroup of those $g$ with $L_0\,\chi g\subseteq L_0$. Let $k$ be an algebraically closed field with $s:\operatorname{Spec}k\to\operatorname{Spec}\mathcal O$ and $u=(E,P)$ a fake elliptic curve with full level-$m$ structure over $k$ which is rigid: every automorphism $e$ of $E$ over $\operatorname{Spec}k$ that is additive for the relative group law on all $T$-points and commutes with the $\Lambda$-action is the identity or acts as inversion on all points. Then any $g\in G$ whose associated automorphism fixes the moduli point, $\mathrm{ptF}(k,s,u)$ followed by $\rho g$ equalling $\mathrm{ptF}(k,s,u)$, lies in $H$.
--
--   This is the rigidity step ensuring that the stabiliser in the level-twisting group $G$ of the fine moduli point of a rigid fake elliptic curve over an algebraically closed field is contained in the right stabiliser $H$ of the line $L_0$; the proof passes through the twist of the level structure by $\chi g$ and the cited construction [`CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist). It feeds the statement comparing Galois frames and stabiliser cardinalities for the moduli tower in the Cerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_mem_of_ptF_comp_eq_of_rigid.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.mem_of_ptF_comp_eq_of_rigid
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    {𝒪 : Type} [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))

    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (hrigid : ∀ (e : u.1.A ≅ u.1.A) (he : e.hom ≫ u.1.f = u.1.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = u.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
      (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u.1.act x) →
      e.hom = 𝟙 u.1.A ∨
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
          mapPt e.hom he P = u.1.L.inv t P)
    (g : G) (hg : (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1) :
    g ∈ H := by sorry
