-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_forall_iso_of_iso_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_forall_iso_of_iso_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e1598144-b9d6-5dd4-be80-5c9684ba1fc6
-- title:
--   Descent of full-level isomorphisms to a finitely generated subalgebra
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ satisfying `IsMaximalOrder`, i.e. $\Lambda$ is an order and is maximal among orders for inclusion; fix naturals $N,m$, a noetherian commutative ring $R$, and a commutative $R$-algebra $L$. Let $u,w$ be objects of `FakeEllipticCurve.WithFullLevel` $\Lambda\,N\,m$ over $R$ — each a fake elliptic curve over the base with $\Lambda$-action and level-$N$ datum, together with a full level-$m$ structure in the sense of `FullLevel` (a section $P$ over the identity which is $m$-torsion for the relative group law, whose $\Lambda$-orbit exhausts the geometric $m$-torsion, and whose $\Lambda$-annihilator is exactly $m\Lambda$) — and let $u',w'$ be such objects over $L$ which are base changes of $u,w$ along the structure map $R \to L$ in the sense of `WithFullLevel.IsPullback` (a morphism $u'.A \to u.A$ forming a pullback square over $\mathrm{Spec}$ of the map, compatible with the group law, the $\Lambda$-action, factorisation through the level subscheme, and the marked point). Assume $u'$ and $w'$ are isomorphic in the sense of `WithFullLevel.Iso`, and let $s$ be a finite subset of $L$. Then there is a finitely generated $R$-subalgebra $T \subseteq L$ containing $s$ such that for every commutative ring $B$ and ring homomorphisms $\varphi : T \to B$, $\chi : R \to B$ with $\varphi$ precomposed by $R \to T$ equal to $\chi$, any objects $u_B,w_B$ over $B$ that are base changes of $u,w$ along $\chi$ satisfy `WithFullLevel.Iso` $u_B\,w_B$.
--
--   This is the spreading-out step for isomorphisms of fake elliptic curves with full level structure: an isomorphism over $L$ already exists over a finitely generated $R$-subalgebra, and hence persists after any further base change out of that subalgebra, in the manner of EGA IV, 8.8.2. It feeds the direct-limit argument `exists_iso_of_iso_of_directed_colimit_of_isUnit` for the Čerednik–Drinfel'd moduli description, where the quantification over all $B$ allows instantiation at an arbitrary stage of the colimit system.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_forall_iso_of_iso_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_forall_iso_of_iso_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (u' w' : FakeEllipticCurve.WithFullLevel Λ N m L)
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) u u')
    (hw : FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R L) w w')
    (he : FakeEllipticCurve.WithFullLevel.Iso u' w') (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∀ (B : Type) [CommRing B] (φ : ↥T →+* B) (χ : R →+* B), φ.comp (algebraMap R ↥T) = χ →
        ∀ (uB wB : FakeEllipticCurve.WithFullLevel Λ N m B),
          FakeEllipticCurve.WithFullLevel.IsPullback χ u uB → FakeEllipticCurve.WithFullLevel.IsPullback χ w wB →
          FakeEllipticCurve.WithFullLevel.Iso uB wB := by sorry
