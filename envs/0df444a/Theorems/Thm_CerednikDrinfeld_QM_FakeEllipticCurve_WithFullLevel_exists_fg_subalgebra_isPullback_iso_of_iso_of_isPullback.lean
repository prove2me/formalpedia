-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7d883158-2c96-54f7-bbe7-f4d483af016a
-- title:
--   Descent of a full-level isomorphism to a finitely generated subalgebra
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. an order contained in no strictly larger order. Let $N,m\in\mathbb{N}$, let $R$ be a noetherian commutative ring and $L$ a commutative $R$-algebra. Let $u,w$ be objects of `FakeEllipticCurve.WithFullLevel Λ N m R`, that is, pairs consisting of a fake elliptic curve over $R$ (a relative group scheme with commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by endomorphisms over the base satisfying the additivity, multiplicativity and trace conditions, and a level-$N$ datum $\mathrm{lev}$) together with a full level-$m$ structure: a section $P$ over the identity which is $m$-torsion, whose $\Lambda$-orbit at every algebraically closed geometric point exhausts the $m$-torsion there, and whose annihilator in $\Lambda$ at every such point is exactly $m\Lambda$. Let $u',w'$ be objects over $L$, and assume each of $u'$ and $w'$ is a pullback of $u$, resp. $w$, along $R\to L$ in the sense of `WithFullLevel.IsPullback`: there is a morphism on total spaces forming a cartesian square over $\operatorname{Spec}$ of the structure map, compatible with the group laws, with the $\Lambda$-actions, carrying points factoring through the level datum to points factoring through the level datum downstairs, and carrying the marked section to the base change of the marked section. Assume $u'\cong w'$ over $L$ in the sense of `WithFullLevel.Iso`: an isomorphism of total spaces over $\operatorname{Spec} L$ respecting the group laws, commuting with the $\Lambda$-actions, matching the level-$N$ factorisation conditions, and sending the marked section of $u'$ to that of $w'$. Then for every finite subset $s\subseteq L$ there is a finitely generated $R$-subalgebra $T\subseteq L$ containing $s$, together with objects $u_T,w_T$ over $T$ that are pullbacks of $u$, resp. $w$, along $R\to T$ in the above sense and satisfy $u_T\cong w_T$.
--
--   This is the spreading-out step for isomorphisms of fake elliptic curves with full level structure: an isomorphism between the base changes to $L$ of two such objects over a noetherian ring $R$ already exists over a finitely generated $R$-subalgebra of $L$, and the finite set $s$ may be absorbed into that subalgebra. It feeds the statement producing, for all larger algebras, compatible isomorphisms of base changes, which is the form used in the representability and coarse moduli arguments for the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_isPullback_iso_of_iso_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (u' w' : FakeEllipticCurve.WithFullLevel Λ N m L)
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) u u')
    (hw : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) w w')
    (he : FakeEllipticCurve.WithFullLevel.Iso u' w') (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (uT wT : FakeEllipticCurve.WithFullLevel Λ N m ↥T),
        FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R ↥T) u uT ∧
        FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R ↥T) w wT ∧
        FakeEllipticCurve.WithFullLevel.Iso uT wT := by sorry
