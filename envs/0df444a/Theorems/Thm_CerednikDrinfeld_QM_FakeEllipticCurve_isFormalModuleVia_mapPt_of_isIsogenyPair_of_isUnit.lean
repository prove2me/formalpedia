-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/9355d57f-9173-523a-9652-9bdaecaef281
-- title:
--   Transport of formal module coordinates along an isogeny of unit degree
-- statement:
--   Fix a prime $r$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ containing $1$, a natural number $N$ and a commutative ring $B$. Let $\mathrm{coord} : \Lambda \to \mathbb{Z}_{r^2} \times \mathbb{Z}_{r^2}$ satisfy `IsOrderCoord`: it is additive, sends $1$ to $(1,0)$, is injective, has dense image modulo every power of $r$, satisfies the twisted multiplication rule involving $r$ and the Witt-vector Frobenius, and records reduced traces. Let $E,E'$ be fake elliptic curves over $B$ of level $N$ with $\Lambda$-action, let $X,X'$ be formal $\mathcal{O}_D$-modules over $B$ for $r$ (two-dimensional commutative formal groups with a $\mathbb{Z}_{r^2}$-action and a uniformiser series $\varpi$), and let $\theta,\theta'$ be $2$-dimensional systems of formal coordinates for $E.f$, resp. $E'.f$, with $\theta$ exhibiting $X$ for $E$ and $\theta'$ exhibiting $X'$ for $E'$ via $\mathrm{coord}$: each is a system of formal coordinates for the relative group law in the sense of `IsFormalCoordinates` (naturality in $B$-algebras, and for each ideal $J$ with $J^{n+1}=0$: infinitesimality, injectivity, surjectivity onto infinitesimal points, and compatibility of the truncated formal group law with the relative group law), and each intertwines the action of $m \in \Lambda$ on points with the series $\mathrm{addVia}$ of $X.\mathrm{act}(\mathrm{coord}\,m)_1$ and $X.\mathrm{act}(\mathrm{coord}\,m)_2 \circ \varpi$. Let $D$ be a natural number whose image in $\mathbb{Z}_{r^2}$ is a unit and with $D \in \Lambda$, and let $q : E.A \to E'.A$, $q' : E'.A \to E.A$ be morphisms over $\mathrm{Spec}\,B$ forming a $\Lambda$-isogeny pair of degree $D$: both are homomorphisms for the relative group laws on points, both commute with the $\Lambda$-actions, and the two composites are the actions of $D$ on $E$ and on $E'$ respectively. Then pushing $\theta$ forward along $q$, i.e. $s \mapsto \mathrm{mapPt}\,q\,(\theta\,s)$, is again a system of formal coordinates exhibiting $E'$ as a formal module via $\mathrm{coord}$ for the same formal $\mathcal{O}_D$-module $X$ (not $X'$).
--
--   This is the step showing that an isogeny of degree prime to the residue characteristic identifies the formal $\mathcal{O}_D$-module structures attached to two fake elliptic curves, so that formal coordinates may be transported across a level isogeny. It is used in the analysis of Atkin–Lehner quotients and level structures in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B : Type} [CommRing B]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (E E' : FakeEllipticCurve Λ N B)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r B) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hE' : E'.IsFormalModuleVia coord X' θ')
    (D : ℕ) (hD : IsUnit ((D : ℕ) : Zp2 r)) (hDΛ : ((D : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (hqq' : FakeEllipticCurve.IsIsogenyPair D E E' q q') :
    E'.IsFormalModuleVia coord X (fun (B' : Type) _ _ (s : Fin 2 → B') => mapPt q hq (θ B' s)) := by sorry
