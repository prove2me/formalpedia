-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_forall_pushPt_act_mapPt_eq_of_character
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.exists_monoidHom_forall_pushPt_act_mapPt_eq_of_character
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7215d724-cef5-5557-a0aa-5343249dd25e
-- title:
--   Level homomorphism normalised by a character κ
-- statement:
--   Fix rationals $a,b,a_1,b_1$, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is an order (contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$ and is finitely generated) and contains every rational integer, and naturals $N$ and $n\neq 0$. Let $\mathcal{O}$ be a commutative ring, $fM : M \to \operatorname{Spec}\mathcal{O}$ a scheme over it, and `ptF` an assignment sending a commutative ring $S$, a morphism $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and a fake elliptic curve over $S$ of level $N$ with full level-$n$ structure to a section of $fM$ over $s$. Let $G$ be a group, $\rho:G\to\operatorname{Aut}M$ a homomorphism and $\chi:G\to\Lambda$ a labelling such that `IsLevelTwistAction` holds: each $\rho(g)$ is a morphism over the base; for $u,u'$ related by a $\chi(g)$-twist isomorphism one has $\mathrm{ptF}(u') = \mathrm{ptF}(u)$ followed by $\rho(g)$; $\chi(1)\equiv 1$ and $\chi(gg')\equiv\chi(g)\chi(g')$ modulo $n\Lambda$; every $c\in\Lambda$ admitting a two-sided inverse modulo $n\Lambda$ is congruent to some $\chi(g)$; and $\chi$ is injective modulo $n\Lambda$. Let $A$ be a fake elliptic curve of level $N$ over a commutative ring $S$, $P$ a full level-$n$ structure on $A$ (a section $P.P$ of $A.f$ over the identity, killed by $n$, whose $\Lambda$-translates give all geometric $n$-torsion, with annihilator exactly $n\Lambda$), $\tilde\Gamma$ a subgroup of $\mathbb{H}[\mathbb{Q},a_1,b_1]^{\times}$, and $e:\tilde\Gamma\to\operatorname{Hom}(A.A,A.A)$ with $e(\gamma)$ followed by $A.f$ equal to $A.f$. Assume there is $\mathrm{lab}:\tilde\Gamma\to\Lambda$ with $e(\gamma)\circ P.P = A.\mathrm{act}(\mathrm{lab}(\gamma))\circ P.P$ for all $\gamma$, with $\mathrm{lab}(\gamma\gamma')\equiv \mathrm{lab}(\gamma')\,\mathrm{lab}(\gamma)$ modulo $n\Lambda$, and with $\mathrm{lab}(\gamma)\equiv c$ modulo $n\Lambda$ whenever $\gamma$ is the scalar $c\in\mathbb{Z}$. Finally let $\kappa:\tilde\Gamma\to(\mathbb{Z}/n)^{\times}$ be a group homomorphism. Then there exists a group homomorphism $\tilde\theta:\tilde\Gamma\to G$ such that for every $\gamma$, translating $e(\gamma)\circ P.P$ by $A.\mathrm{act}(\chi(\tilde\theta(\gamma)))$ equals translating $P.P$ by $A.\mathrm{act}$ of the integer representative $(\kappa(\gamma)).\mathrm{val}$, viewed in $\Lambda$.
--
--   This provides the level homomorphism $\tilde\theta$ attached to a group of quasi-endomorphisms of a fake elliptic curve with full level-$n$ structure, normalised so that the combined action on the level structure is multiplication by the prescribed character $\kappa$; the case $\kappa = 1$ is the unnormalised version. It feeds the fine-moduli statement producing a level homomorphism translating a fibre of a family of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_exists_monoidHom_forall_pushPt_act_mapPt_eq_of_character.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsLevelTwistAction.exists_monoidHom_forall_pushPt_act_mapPt_eq_of_character
    {a b a₁ b₁ : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (N n : ℕ) [NeZero n]
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {fM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)
    {S : Type} [CommRing S] (A : FakeEllipticCurve Λ N S) (P : A.FullLevel n)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (e : ↥Γt → (A.A ⟶ A.A)) (he : ∀ γ, e γ ≫ A.f = A.f)
    (hlab : ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P.P = pushPt (A.act (lab γ)) (A.act_over (lab γ)) P.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])))
    (κ : ↥Γt →* (ZMod n)ˣ) :
    ∃ θt : ↥Γt →* G,
      ∀ γ : ↥Γt, pushPt (A.act (χ (θt γ))) (A.act_over (χ (θt γ))) (mapPt (e γ) (he γ) P.P) =
        pushPt (A.act ⟨((((κ γ : (ZMod n)ˣ) : ZMod n).val : ℤ) : ℚ), hΛℤ _⟩) (A.act_over _) P.P := by sorry
