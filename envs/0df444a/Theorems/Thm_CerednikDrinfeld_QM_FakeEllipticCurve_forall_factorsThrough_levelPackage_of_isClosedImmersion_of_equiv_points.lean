-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_levelPackage_of_isClosedImmersion_of_equiv_points
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_levelPackage_of_isClosedImmersion_of_equiv_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/20b19c23-4787-5c18-9d33-fd87b5e1d877
-- title:
--   Finite étale reduced closed subgroup with (ℤ/n)² points satisfies level axioms
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a nonzero natural number $n$, and an algebraically closed field $k$ in which $n \neq 0$. Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $k$: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$ that is smooth and proper with connected fibres of topological Krull dimension $2$, a commutative relative group law $E.L$ on the functor of points of $E.f$, an action $x \mapsto E.act\,x$ of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$ compatible with the group law and with the ring structure of $\Lambda$, together with its further curve and trace data. Let $g : B \to \operatorname{Spec} k$ be a scheme over $k$ carrying a relative group law $LB$, and let $i$ be a morphism $i.1 : B \to E.A$ with $i.1$ followed by $E.f$ equal to $g$. Assume: $B$ is reduced, $g$ is finite and étale, $i.1$ is a closed immersion; composition with $i$ carries $LB$-multiplication of $T$-points of $g$ to $E.L$-multiplication, for every $k$-scheme $T$; $S$ is a set of sections of $E.f$ over $\operatorname{Spec} k$; there is a bijection $eB$ from the sections of $g$ over $\operatorname{Spec} k$ onto $S$ given by composition with $i$; there is a bijection $e : \mathbb{Z}/n \times \mathbb{Z}/n \to S$ taking addition to $E.L$-multiplication of $k$-points; and $S$ is stable under $P \mapsto P \circ$ (more precisely, pushforward of $P$ along) $E.act\,m$ for every $m \in \Lambda$. Say that a $T$-point $P$ of $E.f$ factors through $i.1$ if $P.1 = P_0$ followed by $i.1$ for some $P_0 : T \to B$. The conclusion is the conjunction of the following. For every $k$-scheme $t : T \to \operatorname{Spec} k$, the $T$-points factoring through $i.1$ are closed under $E.L$-multiplication and $E.L$-inversion, contain the identity section $E.L.one\,t$, are killed by $n$ in the sense that the $n$-fold $E.L$-multiple of such a point equals $E.L.one\,t$, and are stable under pushforward along $E.act\,x$ for every $x \in \Lambda$. Moreover $i.1$ followed by $E.f$ is finite, flat and locally of finite presentation, with fibre rank $n^2$ at every point of $\operatorname{Spec} k$; for every algebraically closed field $k'$ with a ring homomorphism $sk : k \to k'$ such that $n \neq 0$ in $k'$, there is a bijection from $\mathbb{Z}/n \times \mathbb{Z}/n$ onto the $k'$-points of $E.f$ (over the geometric point given by $sk$) that factor through $i.1$, taking addition to $E.L$-multiplication; and a $k$-point of $E.f$ factors through $i.1$ precisely when it lies in $S$.
--
--   The conclusion is exactly the package of axioms demanded of a level-$n$ structure on a fake elliptic curve — subgroup-functor closure, $n$-torsion, $\Lambda$-stability, finiteness, flatness, finite presentation, rank $n^2$, geometric fibres isomorphic to $(\mathbb{Z}/n)^2$, and identification of the $k$-points with $S$ — verified for a reduced finite étale closed subgroup scheme whose $k$-points form a $\Lambda$-stable copy of $(\mathbb{Z}/n)^2$. It is used in the construction of fake elliptic curves with extra level structure, where an abstract subgroup of $k$-points must be upgraded to a genuine level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_levelPackage_of_isClosedImmersion_of_equiv_points.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_levelPackage_of_isClosedImmersion_of_equiv_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ}
    (n : ℕ) [NeZero n] (k : Type) [Field k] [IsAlgClosed k] (hnk : (n : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (B : Scheme.{0}) (g : B ⟶ Spec (CommRingCat.of k)) (LB : RelativeGroupLaw k g) (i : SchemeHomOver g E.f)
    (hred : IsReduced B) (hfin : IsFinite g) (hget : Etale g) (hci : IsClosedImmersion i.1)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
        E.L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i))
    (S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g ≃ ↥S)
    (heB : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
      ((eB y : ↥S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) = NeronModelInfra.schemeHomOverComp y i)
    (e : ZMod n × ZMod n ≃ ↥S)
    (he : ∀ x y : ZMod n × ZMod n,
      ((e (x + y) : ↥S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
        E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hstab : ∀ (m : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f),
      P ∈ S → pushPt (E.act m) (E.act_over m) P ∈ S) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      FactorsThrough i.1 P → FactorsThrough i.1 Q → FactorsThrough i.1 (E.L.mul t P Q) ∧ FactorsThrough i.1 (E.L.inv t P)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough i.1 (E.L.one t)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough i.1 P → nsmulPt E.L t n P = E.L.one t) ∧
    (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough i.1 P → FactorsThrough i.1 (pushPt (E.act x) (E.act_over x) P)) ∧
    IsFinite (i.1 ≫ E.f) ∧ Flat (i.1 ≫ E.f) ∧ LocallyOfFinitePresentation (i.1 ≫ E.f) ∧
    (∀ s : ↥(Spec (CommRingCat.of k)), (i.1 ≫ E.f).finrank s = n ^ 2) ∧
    (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), (n : k') ≠ 0 →
      ∃ e' : ZMod n × ZMod n ≃ {P : SchemeHomOver (geomPoint k' sk) E.f // FactorsThrough i.1 P},
        ∀ x y : ZMod n × ZMod n, (e' (x + y) : SchemeHomOver (geomPoint k' sk) E.f) = E.L.mul (geomPoint k' sk) (e' x) (e' y)) ∧
    (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough i.1 P ↔ P ∈ S) := by sorry
