-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsLevelTwistAction_finite_of_isOrder
-- name    : CerednikDrinfeld.QM.IsLevelTwistAction.finite_of_isOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/2cfa80cc-6754-5d87-979b-b567472049ef
-- title:
--   A level-twist action is by a finite group
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated. Fix natural numbers $N$ and $m$ with $m > 0$, a commutative ring $B$, a scheme $M$ with a morphism $\pi_M : M \to \operatorname{Spec} B$, and a family $\mathrm{ptF}$ which assigns to every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ datum together with a full level-$m$ structure on it, a morphism $\operatorname{Spec} S \to M$ over $s$. Fix a group $G$, a homomorphism $\rho : G \to \operatorname{Aut} M$ and a map $\chi : G \to \Lambda$, and assume `IsLevelTwistAction` holds for these data: every $\rho(g)$ is a morphism over $\operatorname{Spec} B$; whenever two families with full level structure over $S$ are related by a twist labelled by $\chi(g)$, the two associated points of $M$ differ by composition with $\rho(g)$; and the labels satisfy $\chi(1) \equiv 1$, $\chi(gg') \equiv \chi(g)\chi(g')$ modulo $m\Lambda$, surjectivity of $\chi$ onto the classes of two-sided units modulo $m\Lambda$, and injectivity of $g \mapsto \chi(g) \bmod m\Lambda$. The conclusion is that $G$ is finite.
--
--   This is the finiteness statement underlying the twisting group in the Čerednik–Drinfeld style description of fine moduli of fake elliptic curves with full level structure: the group acting by level twists on the moduli scheme is finite because its labels inject into $\Lambda/m\Lambda$. It is used in the identification of fibres of the fine family and in the criterion describing when two points of the fine family coincide.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsLevelTwistAction_finite_of_isOrder.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.IsLevelTwistAction.finite_of_isOrder
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N m : ℕ} (hm : 0 < m)
    {B : Type} [CommRing B] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) : Finite G := by sorry
