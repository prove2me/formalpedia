-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hom_eq_of_comp_eq_of_isPullback_fstHom
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.hom_eq_of_comp_eq_of_isPullback_fstHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/3410e8ad-9f4f-5608-8bbf-6c4cba905156
-- title:
--   Rigidity of homomorphisms of fake elliptic curves over dual numbers
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a field $k$, and write $k[\varepsilon]=\mathrm{DualNumber}\;k$. Let $E$ be a fake elliptic curve over $k$ and let $t,t'$ be fake elliptic curves over $k[\varepsilon]$; here a fake elliptic curve over a commutative ring $S$ consists of a scheme with a morphism $f$ to $\operatorname{Spec} S$, a commutative relative group law $L$ on its functor of points over $\operatorname{Spec} S$, the property bundle asserting that $f$ is smooth, proper and has connected fibres and admits a relative group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base that are homomorphisms for $L$ and are additive and anti-multiplicative in $\Lambda$ with the prescribed trace on tangent vectors at geometric points, together with further level-$N$ data. Let $g : E.A \to t.A$ be a morphism making the square formed by $g$, $E.f$, $t.f$ and $\operatorname{Spec}$ of the projection $k[\varepsilon] \to k$, $\varepsilon \mapsto 0$, cartesian, so that $E.A$ is the closed fibre of $t.A$. Let $e_1,e_2 : t.A \to t'.A$ be morphisms over $\operatorname{Spec} k[\varepsilon]$, i.e. $e_i$ followed by $t'.f$ equals $t.f$, and assume each $e_i$ is a homomorphism of group laws on points: for every scheme $T$, every $t'' : T \to \operatorname{Spec} k[\varepsilon]$ and all $T$-points $P,Q$ of $t.A$ over $t''$, composing the product $t.L.\mathrm{mul}\,t''\,P\,Q$ with $e_i$ gives the product in $t'.L$ of $P$ followed by $e_i$ and $Q$ followed by $e_i$. If $g$ followed by $e_1$ equals $g$ followed by $e_2$, then $e_1 = e_2$.
--
--   This is the rigidity statement for homomorphisms of first-order deformations of a fake elliptic curve: a homomorphism over the dual numbers is determined by its restriction to the closed fibre. It is used in the quaternionic moduli part of the Čerednik–Drinfeld material, where it feeds the uniqueness assertions [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_comp_hom_eq_of_isPullbackVia_fstHom`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_comp_hom_eq_of_isPullbackVia_fstHom) and [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_of_iso_comp_eq`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_of_iso_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hom_eq_of_comp_eq_of_isPullback_fstHom.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory
open AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hom_eq_of_comp_eq_of_isPullback_fstHom
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {k : Type u} [Field k] (E : FakeEllipticCurve Λ N k) (t t' : FakeEllipticCurve Λ N (DualNumber k))
    (g : E.A ⟶ t.A)
    (hg : CategoryTheory.IsPullback g E.f t.f
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))
    (e₁ e₂ : t.A ⟶ t'.A) (he₁ : e₁ ≫ t'.f = t.f) (he₂ : e₂ ≫ t'.f = t.f)
    (hom₁ : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t'' t.f),
      mapPt e₁ he₁ (t.L.mul t'' P Q) = t'.L.mul t'' (mapPt e₁ he₁ P) (mapPt e₁ he₁ Q))
    (hom₂ : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t'' t.f),
      mapPt e₂ he₂ (t.L.mul t'' P Q) = t'.L.mul t'' (mapPt e₂ he₂ P) (mapPt e₂ he₂ Q))
    (h : g ≫ e₁ = g ≫ e₂) : e₁ = e₂ := by sorry
