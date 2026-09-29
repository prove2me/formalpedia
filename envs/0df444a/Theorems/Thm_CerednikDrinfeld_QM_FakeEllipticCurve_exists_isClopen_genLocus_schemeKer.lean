-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClopen_genLocus_schemeKer
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClopen_genLocus_schemeKer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/dcb90ee8-af93-5522-a124-4faf90ebb302
-- title:
--   Clopen locus of full level-m generators in A[m]
-- statement:
--   Fix $a,b\in\mathbb Q$ and primes $q,q'$, and suppose $\mathbb H[\mathbb Q,a,b]$ is indefinite and ramified exactly at $q$ and $q'$, in the sense that $0<a$ or $0<b$ and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders, let $N,m\in\mathbb N$, let $S$ be a commutative ring in which the image of $m$ is a unit, and let $E$ be a fake elliptic curve of level $N$ over $S$ for $\Lambda$: a scheme $E.A$ over $\operatorname{Spec} S$ carrying a commutative relative group law $E.L$, the abelian-scheme property bundle, fibres of dimension $2$, an action of $\Lambda$ by endomorphisms over $S$ compatible with the group law and satisfying the reduced-trace condition, together with the level data. Write $A[m]$ for `E.L.schemeKer m`, the pullback of multiplication by $m$, i.e. of `E.L.schemeNsmul m`, along the unit section over $\operatorname{Spec} S$. The assertion is that there is an open subscheme $\mathcal G$ of $A[m]$ whose underlying set is also closed, such that for every algebraically closed field $k$, every ring homomorphism $sk:S\to k$ and every point $P$ of $E.A$ over the geometric point $\operatorname{Spec} k\to\operatorname{Spec} S$ induced by $sk$ with $m\cdot P$ equal to the unit section, the following are equivalent: (i) $P$ lifts to a morphism $\kappa:\operatorname{Spec} k\to A[m]$ whose composite with the first pullback projection is $P$ and whose set-theoretic range lies in $\mathcal G$; (ii) every $m$-torsion point $Q$ over that geometric point is of the form $x\cdot P$ for some $x\in\Lambda$, and for $x\in\Lambda$ one has $x\cdot P$ equal to the unit section exactly when $x=m y$ for some $y\in\Lambda$.
--
--   This is the Katz–Mazur style statement that the locus of full level-$m$ structures, here generators of the $\Lambda$-module $A[m]$, is open and closed in the finite étale $m$-torsion scheme of a fake elliptic curve, characterised by its geometric points. It is used in the construction of the auxiliary full-level fake elliptic curve over a flat surjective base change and in the computation of the annihilator of a generator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isClopen_genLocus_schemeKer.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicGeometry
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isClopen_genLocus_schemeKer
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m : ℕ)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) :
    ∃ 𝒢 : (E.L.schemeKer m).Opens, IsClosed (𝒢 : Set ↥(E.L.schemeKer m)) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (P : SchemeHomOver (geomPoint k sk) E.f),
        nsmulPt E.L (geomPoint k sk) m P = E.L.one (geomPoint k sk) →
        ((∃ κ : Spec (CommRingCat.of k) ⟶ E.L.schemeKer m,
            κ ≫ pullback.fst (E.L.schemeNsmul m) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 = P.1 ∧
            Set.range κ ⊆ (𝒢 : Set ↥(E.L.schemeKer m))) ↔
          ((∀ Q : SchemeHomOver (geomPoint k sk) E.f, nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
              ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) P = Q) ∧
           (∀ x : ↥Λ, pushPt (E.act x) (E.act_over x) P = E.L.one (geomPoint k sk) ↔
              ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])))) := by sorry
