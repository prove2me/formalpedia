-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_isFormalCoordinates
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/9b13dcce-75ef-5f19-acd9-a9e746927996
-- title:
--   Formal mathcal O_D-module structure from a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a natural number $N$ and a prime $q$. Let $\mathrm{coord}:\Lambda\to \mathrm{Zp2}\,q\times \mathrm{Zp2}\,q$, with values in pairs of Witt vectors over $\mathrm{GF}(q^2)$, satisfy `IsOrderCoord`: it is additive, sends $1$ (when $1\in\Lambda$) to $(1,0)$, is multiplicative for the twisted rule $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+q\beta\,\sigma\beta',\ \alpha\beta'+\beta\,\sigma\alpha')$ with $\sigma$ the Witt-vector Frobenius, is injective, has image dense for the $q$-adic filtration in each coordinate, and satisfies $\alpha_m+\sigma\alpha_m=n$ whenever $m+\bar m=n\in\mathbb Z$. Let $B$ be a commutative ring in which the image of $q$ is nilpotent, $E$ a `FakeEllipticCurve` for $\Lambda$ of level $N$ over $B$ (an abelian scheme $f:A\to\operatorname{Spec}B$ with relative group law $E.L$, commutative, of fibre dimension $2$, carrying a $\Lambda$-action by endomorphisms compatible with addition, multiplication and traces), $F$ a commutative $2$-dimensional formal group law over $B$, and $\theta$ a system of formal coordinates for $f$ in $2$ variables such that `E.L.IsFormalCoordinates F θ` holds: $\theta$ is natural in $B$-algebras, and for every $B$-algebra $B'$ and nilpotent ideal $J$ it parametrises bijectively the $J$-infinitesimal points of $E$ by nilpotent coordinate tuples in $J$, transporting the truncated $F$-addition to $E.L$'s multiplication. Then there exists a formal $\mathcal O_D$-module $X$ over $B$ (a commutative $2$-dimensional law together with series $[\alpha]_X$ for $\alpha\in\mathrm{Zp2}\,q$ and $\varpi_X$, all endomorphisms of the law, with $[\,\cdot\,]$ additive and multiplicative, $[1]=\mathrm{id}$, $\varpi_X\circ\varpi_X=[q]$ and $\varpi_X\circ[\alpha]=[\sigma\alpha]\circ\varpi_X$) whose underlying law $X.F$ equals $F$ and which is the formal module of $E$ in the coordinates $\theta$: for every $m\in\Lambda$ with $\mathrm{coord}(m)=(\alpha_m,\beta_m)$, the series $[\alpha_m]_X +_{F} [\beta_m]_X\circ\varpi_X$, evaluated on nilpotent tuples, computes the action of $E.act\ m$ on the corresponding infinitesimal points of $E$.
--
--   This is the algebraic step in the construction of the formal $\mathcal O_D$-module attached to a fake elliptic curve over a base in which $q$ is nilpotent: the quaternionic action on the abelian surface is transported to the $2$-dimensional formal group along given formal coordinates, and the resulting ring action of $\Lambda$ extends to the maximal order $\mathcal O_D$ of the quaternion division algebra over $\mathbb Q_q$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_isFormalModuleOf`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_isFormalModuleOf), which combines it with the local existence of formal coordinates on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFormalModuleVia_of_isFormalCoordinates.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFormalModuleVia_of_isFormalCoordinates
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (F : MvFormalGroup 2 B) (hF : F.IsComm) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ : E.L.IsFormalCoordinates F θ) :
    ∃ X : FormalODModule q B, X.F = F ∧ E.IsFormalModuleVia coord X θ := by sorry
