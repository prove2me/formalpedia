-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/fc3d5727-5a41-5a46-a08f-8e14dd503a16
-- title:
--   Unique mathcal O_D-linear formal completion of a Λ-equivariant endomorphism
-- statement:
--   Fix a prime $q$, rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, and a map $\mathrm{coord}\colon\Lambda\to W(\mathbb F_{q^2})^2$ satisfying `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, satisfies the twisted multiplication rule $\mathrm{coord}(mm')=(\alpha\alpha'+q\beta\,\varphi(\beta'),\ \alpha\beta'+\beta\,\varphi(\alpha'))$ with $\varphi$ the Witt-vector Frobenius, has $q$-adically dense image in each coordinate, and satisfies $\alpha_m+\varphi(\alpha_m)=n$ whenever $m+\bar m=n\in\mathbb Z$. Let $N\in\mathbb N$, let $B$ be a commutative ring in which $q$ is nilpotent, let $E$ be a fake elliptic curve over $B$ with $\Lambda$-action and level $N$ (structure `FakeEllipticCurve`), let $X$ be a formal $\mathcal O_D$-module over $B$ (a commutative two-dimensional formal group law $X.F$ with a $W(\mathbb F_{q^2})$-action by one-variable-indexed series and a series $\varpi$ with $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\varphi(a)]\circ\varpi$), and let $\theta$ be a system of $2$-dimensional formal coordinates for $E.f$ (for each $B$-algebra $B'$ a map from pairs in $B'$ to $B'$-points of $E$ over $B$) with `IsFormalModuleVia`: $\theta$ transports the group law $E.L$ into $X.F$, and for every $B$-algebra $B'$, ideal $J$ with $J^{n+1}=0$, every $m\in\Lambda$ and every pair $s$ of elements of $J$, $\theta$ applied to the truncated evaluation at $s$ of $X.F$-sum of $[\alpha_m]$ and $[\beta_m]\circ\varpi$ equals the image of $\theta(s)$ under $E.\mathrm{act}\,m$. Let $f\colon E.A\to E.A$ satisfy $f$ followed by $E.f$ equals $E.f$, be a homomorphism for $E.L$ on $T$-points for all $T$, and commute with $E.\mathrm{act}\,m$ for every $m\in\Lambda$. Then there is exactly one element $u$ of the centraliser, in the endomorphism ring of the law $X.F$, of the set of all $X.\mathrm{actEnd}\,a$ together with $X.\mathrm{varpiEnd}$, whose tuple of power series is the formal completion of $f$ along $\theta$, i.e. for every $B$-algebra $B'$, ideal $J$ with $J^{n+1}=\bot$ and pair $s$ of elements of $J$, $\theta$ of the truncated evaluation of those series at $s$ equals the image of $\theta(s)$ under $f$.
--
--   This is the statement that a $\Lambda$-equivariant endomorphism of a fake elliptic curve in the Čerednik–Drinfeld setting induces a unique $\mathcal O_D$-linear endomorphism of its formal $\mathcal O_D$-module, the endomorphism ring of the latter being realised as the centraliser of the $W(\mathbb F_{q^2})$-action and of $\varpi$ inside the endomorphism ring of the underlying formal group law. It feeds the passage from such endomorphisms to elements of $\mathrm{GL}_2$ acting on the Bruhat–Tits tree, used by the two results on existence of a general linear group element realising the completion up to conjugation and scaling.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia
    {q : ℕ} [Fact q.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (q : B))

    (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ : E.IsFormalModuleVia coord X θ)

    (f : E.A ⟶ E.A) (hf : f ≫ E.f = E.f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
      pushPt f hf (E.L.mul t P Q) = E.L.mul t (pushPt f hf P) (pushPt f hf Q))
    (hlin : ∀ m : ↥Λ, E.act m ≫ f = f ≫ E.act m) :
    ∃! u : Subring.centralizer (Set.range X.actEnd ∪ {X.varpiEnd}),
      IsFormalCompletionAlong θ θ f hf (MvFormalGroup.Hom.toPowerSeries (u : MvFormalGroup.End X.F)) := by sorry
