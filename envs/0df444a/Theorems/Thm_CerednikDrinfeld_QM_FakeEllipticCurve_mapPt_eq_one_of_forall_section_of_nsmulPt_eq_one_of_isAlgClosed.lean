-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_eq_one_of_forall_section_of_nsmulPt_eq_one_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_eq_one_of_forall_section_of_nsmulPt_eq_one_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/55a83e3a-74f9-559e-8d61-5c7e4e1a2e4d
-- title:
--   Endomorphism conditions on n-torsion descend from k₀-points
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ and a natural number $N$, let $k_0$ be an algebraically closed field, and let $E$ be a `FakeEllipticCurve` for $\Lambda$, $N$ over $k_0$, so in particular $E$ provides a scheme $E.A$, a structure morphism $E.f : E.A \to \operatorname{Spec} k_0$ and a commutative relative group law $E.L$ on the functor of sections $T \mapsto \{\varphi : T \to E.A \mid \varphi \text{ over } E.f\}$, together with the remaining data of that structure. Let $n$ be a natural number invertible in the sense that $n \ne 0$ in $k_0$, let $(g_i)_{i \in \iota}$ be an arbitrary family of endomorphisms of $E.A$ with $g_i$ followed by $E.f$ equal to $E.f$, and let $h$ be one further such endomorphism. Assume the pointwise hypothesis: for every section $Q_0$ of $E.f$ over $\mathrm{id}_{\operatorname{Spec} k_0}$ whose $n$-fold sum $\mathrm{nsmulPt}\,E.L\,n\,Q_0$ (iterated `E.L.mul` starting from `E.L.one`) equals the unit section, and with $Q_0$ followed by each $g_i$ equal to the unit section, the composite of $Q_0$ with $h$ is the unit section. Then for every scheme $T$, every $t : T \to \operatorname{Spec} k_0$ and every section $P$ of $E.f$ over $t$ with $\mathrm{nsmulPt}\,E.L\,t\,n\,P = E.L.\mathrm{one}\,t$ and $P$ followed by each $g_i$ equal to $E.L.\mathrm{one}\,t$, the section $P$ followed by $h$ equals $E.L.\mathrm{one}\,t$.
--
--   This is the passage from $k_0$-rational points to arbitrary $T$-valued points for conditions cut out by endomorphisms on $n$-torsion, $n$ invertible on the base: a closed condition verified on all $n$-torsion points with values in the algebraically closed base field automatically holds for $n$-torsion sections over any base scheme. It is used in the study of the endomorphism action on torsion of fake elliptic curves, in particular by the results identifying when all $\mathrm{mapPt}$ conditions force a point to be trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_eq_one_of_forall_section_of_nsmulPt_eq_one_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_eq_one_of_forall_section_of_nsmulPt_eq_one_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (E : FakeEllipticCurve Λ N k₀) (n : ℕ) (hn : (n : k₀) ≠ 0)
    {ι : Type} (g : ι → (E.A ⟶ E.A)) (hg : ∀ i, g i ≫ E.f = E.f) (h : E.A ⟶ E.A) (hh : h ≫ E.f = E.f)
    (hyp : ∀ Q₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k₀))) n Q₀ = E.L.one (𝟙 (Spec (CommRingCat.of k₀))) →
      (∀ i, mapPt (g i) (hg i) Q₀ = E.L.one (𝟙 (Spec (CommRingCat.of k₀)))) →
      mapPt h hh Q₀ = E.L.one (𝟙 (Spec (CommRingCat.of k₀))))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t E.f)
    (hP : nsmulPt E.L t n P = E.L.one t) (hgP : ∀ i, mapPt (g i) (hg i) P = E.L.one t) :
    mapPt h hh P = E.L.one t := by sorry
