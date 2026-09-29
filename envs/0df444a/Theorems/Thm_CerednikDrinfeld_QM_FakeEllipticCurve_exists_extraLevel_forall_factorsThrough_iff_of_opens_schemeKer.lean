-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e63e2506-df77-5ce7-a23d-d6987c41f1ed
-- title:
--   Admissible clopen subset of A[N] gives an extra level
-- statement:
--   Let $a,b\in\mathbb Q$, let $\Lambda$ be a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, let $S$ be a commutative ring, and let $E$ be a fake elliptic curve over $S$ with $\Lambda$-action and level parameter $1$, with structure morphism $E.f\colon E.A\to\operatorname{Spec}S$ and relative group law $E.L$. Let $N$ be a non-zero natural number whose image in $S$ is a unit, write $\iota\colon E.L.\mathrm{schemeKer}\,N=E.A\times_{E.A}\operatorname{Spec}S\to E.A$ for the first projection of the pullback of multiplication by $N$ along the unit section, and let $U$ be an open subscheme of $E.L.\mathrm{schemeKer}\,N$ whose underlying set is closed. Say that a point $P\in E.A(T)$ over $t\colon T\to\operatorname{Spec}S$ lies in $U$ if $P$ factors as $P_0$ followed by $U.\iota\;\text{then}\;\iota$ for some $P_0\colon T\to U$. Assume: the points lying in $U$ are closed under the group law and inversion; the unit point over every $t$ lies in $U$; they are stable under $\mathrm{pushPt}$ by every $E.\mathrm{act}\,x$, $x\in\Lambda$; the finite rank of $U$ over $\operatorname{Spec}S$ is $N^2$ at every point; and for every algebraically closed field $k$ and ring map $sk\colon S\to k$ with $N\neq0$ in $k$ there is a bijection $\mathbb Z/N\times\mathbb Z/N\to\{P\in E.A(\operatorname{Spec}k)\ \text{lying in}\ U\}$ carrying addition to the group law. Then there exists an extra level structure $K$ of order $N$ on $E$ — a scheme with a closed immersion $K.\mathrm{levK}$ into $E.A$, whose factoring points form a $\Lambda$-stable subgroup killed by $N$ meeting $E.\mathrm{lev}$ only in the unit, with $K$ finite, flat and locally of finite presentation over $S$ of rank $N^2$ and geometric fibres $(\mathbb Z/N)^2$ — such that for all $t\colon T\to\operatorname{Spec}S$ and all $P\in E.A(T)$ over $t$, $P$ factors through $K.\mathrm{levK}$ if and only if $P$ lies in $U$.
--
--   This is the recognition step for level structures on fake elliptic curves: an open-and-closed subgroup-like subset of the $N$-torsion, of the expected rank and with the expected geometric fibres, is exactly the locus of an extra level of order $N$. It is used in the construction of a finite étale scheme representing extra level structures, via [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_finite_etale_represents_extraLevel`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_finite_etale_represents_extraLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_opens_schemeKer
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ 1 S) (N : ℕ) [NeZero N] (hN : IsUnit ((N : ℕ) : S))
    (U : (E.L.schemeKer N).Opens) (hUc : IsClosed (U : Set ↥(E.L.schemeKer N)))
    (hsub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) Q →
        FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
            (E.L.mul t P Q) ∧
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
            (E.L.inv t P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
        (E.L.one t))
    (hstab : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P →
        FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1)
          (pushPt (E.act x) (E.act_over x) P))
    (hrank : ∀ s : ↥(Spec (CommRingCat.of S)), (U.ι ≫ E.L.schemeKerStr N).finrank s = N ^ 2)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃
          {P : SchemeHomOver (geomPoint k sk) E.f //
            FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y)) :
    ∃ K : E.ExtraLevel N,
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔
          FactorsThrough (U.ι ≫ pullback.fst (E.L.schemeNsmul N) (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1) P := by sorry
