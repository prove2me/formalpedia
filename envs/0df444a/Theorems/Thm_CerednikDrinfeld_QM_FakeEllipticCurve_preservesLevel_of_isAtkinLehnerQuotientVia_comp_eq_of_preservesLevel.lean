-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/0fce2150-7a54-5201-83d0-c42dc42dedfa
-- title:
--   Second factor through an Atkin–Lehner quotient preserves level
-- statement:
--   Fix natural numbers $r$, $\bar r$, $N$ with $r$ and $\bar r$ prime, $N \neq 0$, $\bar r \neq r$ and $\bar r \nmid N$, and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b r rbar` holds, i.e. $0 < a$ or $0 < b$, and for a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order (containing $1$, closed under multiplication, spanning the algebra over $\mathbb{Q}$, finitely generated) and maximal among orders containing it, and let $k_0$ be an algebraically closed field of characteristic $r$. Let $A_0$ and $A_{0,w}$ be fake elliptic curves over $k_0$ of level $N$ for $\Lambda$ (a scheme over $\operatorname{Spec} k_0$ with a commutative relative group law on its functor of points, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ compatible with the group law and with reduced traces, and a level morphism `lev`). Let $aw : A_0.A \to A_{0,w}.A$ and $aw' : A_{0,w}.A \to A_0.A$ be morphisms over $\operatorname{Spec} k_0$ satisfying `IsAtkinLehnerQuotientVia rbar`: both are additive on $T$-points, both commute with the $\Lambda$-actions, their two composites are the action of the scalar $\bar r$ whenever $\bar r \in \Lambda$, a $T$-point $P$ of $A_0$ is killed by $aw$ precisely when it is killed by every $m \in \Lambda$ with $m \bar m = \bar r n$ for some $n \in \mathbb{Z}$, and $aw$ carries points factoring through $A_0.\mathrm{lev}$ to points factoring through $A_{0,w}.\mathrm{lev}$. Let further $f : A_0.A \to A_0.A$ be a morphism over $\operatorname{Spec} k_0$ which preserves the level, in the sense that for every $T$ and every $T$-point $P$ of $A_0$ over $\operatorname{Spec} k_0$ factoring through $A_0.\mathrm{lev}$ the composite $P$ followed by $f$ again factors through $A_0.\mathrm{lev}$, and let $bw : A_{0,w}.A \to A_0.A$ be a morphism over $\operatorname{Spec} k_0$ that is additive on $T$-points and satisfies $bw \circ aw = f$. Then $bw$ preserves the level: every $T$-point of $A_{0,w}$ factoring through $A_{0,w}.\mathrm{lev}$ is sent by $bw$ to a point factoring through $A_0.\mathrm{lev}$.
--
--   In the Čerednik–Drinfeld analysis of fake elliptic curves in characteristic $r$, endomorphisms of the mod-$r$ fibre are factored through the Atkin–Lehner quotient at $\bar r$; this statement transfers the level-preservation property from the composite $f$ to the second factor $bw$. It is used in the construction of an Atkin–Lehner quotient together with an isogeny pair whose composite is a prescribed action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isAtkinLehnerQuotientVia_comp_eq_of_preservesLevel
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrbarN : ¬ rbar ∣ N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ A₀w : FakeEllipticCurve Λ N k₀)
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (hAL : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (f : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf_lev : FakeEllipticCurve.PreservesLevel A₀ A₀ f hf)
    (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f)
    (hbw_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀w.f),
      mapPt bw hbw (A₀w.L.mul t P Q) = A₀.L.mul t (mapPt bw hbw P) (mapPt bw hbw Q))
    (hcomp : aw ≫ bw = f) :
    FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw := by sorry
