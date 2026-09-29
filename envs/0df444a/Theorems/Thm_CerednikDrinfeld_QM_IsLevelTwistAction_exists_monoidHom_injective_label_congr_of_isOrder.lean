-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_injective_label_congr_of_isOrder
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.exists_monoidHom_injective_label_congr_of_isOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/97580b53-9fbb-5759-aa98-eb80bcaba898
-- title:
--   Label-compatible injection between level-twisting groups
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of `IsOrder`: it contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, and is finitely generated. Fix natural numbers $N,m$. Given two base rings $B_0$ and $\mathcal{O}$, schemes $M_0$, $M$ with structure morphisms $\pi_{M_0} : M_0 \to \operatorname{Spec} B_0$ and $\pi_M : M \to \operatorname{Spec}\mathcal{O}$, and point-assignments $\mathrm{ptF}_0$, $\mathrm{ptF}$ sending, for each ring $S$ and each morphism $s : \operatorname{Spec} S \to$ the base, a fake elliptic curve over $S$ for $(\Lambda,N)$ with a full level-$m$ structure to a morphism over $s$ to the moduli scheme, suppose groups $G_0$, $G$ act through homomorphisms $\rho_0 : G_0 \to \operatorname{Aut} M_0$, $\rho : G \to \operatorname{Aut} M$ with label maps $\chi_0 : G_0 \to \Lambda$, $\chi : G \to \Lambda$, and that both data satisfy `IsLevelTwistAction`: each automorphism lies over the base, it realises the $\chi(g)$-twisting of moduli points, and the labels satisfy $\chi(1) \equiv 1$, $\chi(gg') \equiv \chi(g)\chi(g')$, surjectivity of $\chi$ onto the classes $c$ admitting a two-sided inverse modulo $m\Lambda$, and injectivity of $\chi$ modulo $m\Lambda$ (congruence meaning the difference lies in $m \cdot \Lambda$ inside $\mathbb{H}[\mathbb{Q},a,b]$). Then there exists an injective group homomorphism $\psi : G \to G_0$ with $\chi_0(\psi(g)) - \chi(g) \in m\cdot\Lambda$ for every $g \in G$.
--
--   This comparison lemma transports a level-twisting action from one base to another: since the labels identify both $G$ and $G_0$ with the group of units of $\Lambda/m\Lambda$, the two twisting groups are matched compatibly with their labels. It is used in the construction and comparison of coarse and fine moduli for fake elliptic curves with full level structure, notably in the quotient and pullback statements for these moduli problems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_injective_label_congr_of_isOrder.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsLevelTwistAction.exists_monoidHom_injective_label_congr_of_isOrder
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (N m : ℕ)
    {B₀ : Type} [CommRing B₀] {M₀ : Scheme.{0}} {πM₀ : M₀ ⟶ Spec (CommRingCat.of B₀)}
    {ptF₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM₀}
    {G₀ : Type} [Group G₀] {ρ₀ : G₀ →* Aut M₀} {χ₀ : G₀ → ↥Λ} (hρ₀ : IsLevelTwistAction Λ N m M₀ πM₀ ptF₀ G₀ ρ₀ χ₀)
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) :
    ∃ ψ : G →* G₀, Function.Injective ψ ∧
      ∀ g : G, ∃ y : ↥Λ, (χ₀ (ψ g) : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by sorry
