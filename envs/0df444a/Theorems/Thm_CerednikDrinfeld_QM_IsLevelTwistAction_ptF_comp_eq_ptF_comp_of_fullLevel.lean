-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_ptF_comp_eq_ptF_comp_of_fullLevel
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.ptF_comp_eq_ptF_comp_of_fullLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/98f0ca13-140b-52fa-bad3-2ee40f5df218
-- title:
--   Moduli point on a G-invariant quotient ignores the full level
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated; fix naturals $N,m$ and a commutative ring $\mathcal{O}$ in which the image of $m$ is a unit. Let $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with an assignment $\mathrm{ptF}$ sending each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair $(E,P)$ consisting of a fake elliptic curve $E$ over $S$ of level $N$ with $\Lambda$-action (an abelian scheme with commutative relative group law, fibres of dimension $2$, a $\Lambda$-action compatible with the group law and the trace condition, and level-$N$ datum) and a full level-$m$ structure $P$ on $E$ (an $m$-torsion section whose $\Lambda$-translates exhaust the $m$-torsion at every algebraically closed geometric point and whose annihilator in $\Lambda$ is exactly $m\Lambda$) to a morphism $\operatorname{Spec} S \to M$ over $\pi_M$ lying above $s$. Assume $(M,\pi_M,\mathrm{ptF})$ satisfies `IsFineModuli`: $\mathrm{ptF}$ is constant on isomorphism classes, compatible with base change along ring homomorphisms, surjective onto morphisms over $\pi_M$, and injective up to isomorphism. Assume further a group $G$, a homomorphism $\rho : G \to \operatorname{Aut} M$ and labels $\chi : G \to \Lambda$ satisfying `IsLevelTwistAction`: each $\rho(g)$ is an automorphism over $\operatorname{Spec}\mathcal{O}$; whenever $u'$ is a $\chi(g)$-twist of $u$ one has $\mathrm{ptF}(u') = \mathrm{ptF}(u)$ followed by $\rho(g)$; and $\chi$ is multiplicative, normalised and bijective modulo $m\Lambda$ onto the classes invertible modulo $m\Lambda$. Let $\pi : M \to X$ satisfy $\rho(g)$ followed by $\pi$ equals $\pi$ for all $g \in G$. Then for every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$, every fake elliptic curve $E$ over $S$ and any two full level-$m$ structures $P,P'$ on $E$, the underlying morphism of $\mathrm{ptF}(S,s,(E,P'))$ followed by $\pi$ equals that of $\mathrm{ptF}(S,s,(E,P))$ followed by $\pi$.
--
--   This is the descent step showing that the moduli point of a fake elliptic curve on a $G$-invariant quotient of a fine moduli scheme is independent of the auxiliary full level-$m$ structure, the $\Lambda^\times$-worth of choices being absorbed by the level-twisting action. It is used to produce a coarse moduli scheme as such a quotient in the Čerednik–Drinfeld setting, via [`CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuli_of_quotient_of_isIndefiniteRamifiedExactlyAt`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuli_of_quotient_of_isIndefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_ptF_comp_eq_ptF_comp_of_fullLevel.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsLevelTwistAction.ptF_comp_eq_ptF_comp_of_fullLevel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛord : IsOrder Λ) {N m : ℕ} {𝒪 : Type} [CommRing 𝒪]
    (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hG : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    {X : Scheme.{0}} (π : M ⟶ X) (hπρ : ∀ g : G, (ρ g).hom ≫ π = π)
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (E : FakeEllipticCurve Λ N S) (P P' : E.FullLevel m) :
    (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π := by sorry
