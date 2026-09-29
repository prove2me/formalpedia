-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange
-- name    : FormalGroup.IsDrinfeldBasisAdic.map_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/6806bbe7-62cd-5c13-aebe-b0d95692c592
-- title:
--   Drinfeld bases transport along base change of formal groups
-- statement:
--   Let $R$ and $S$ be commutative rings, $I \subseteq R$ and $J \subseteq S$ ideals with respect to which $R$ and $S$ are adically complete, and let $f : R \to S$ be a ring homomorphism carrying $I$ into $J$ (that is, $f r \in J$ for every $r \in I$). Let $F$ be a formal group over $R$ and $G$ a formal group over $S$, and assume $F.\mathrm{IsBaseChange}\,f\,G$, i.e. the defining multivariate power series of $G$ is obtained from that of $F$ by applying $f$ coefficientwise: `G.toPowerSeries = MvPowerSeries.map f F.toPowerSeries`. Let $q$ be a natural number and $x_0, x_1$ elements of $I$, and suppose $F$ has `IsDrinfeldBasisAdic` for $I$, $q$, $x_0$, $x_1$: with $R$ equipped with the ideal $I$ (so with the $I$-adic structure used to form the divisor series), there is a unit $u \in R[\![X]\!]$ with $F.\mathrm{nthSeries}\,q = u \cdot F.\mathrm{drinfeldDivisor}\,q\,x_0\,x_1$. The conclusion is the corresponding statement over $S$: $G$ has `IsDrinfeldBasisAdic` for $J$, $q$, $f x_0$, $f x_1$, i.e. relative to the ideal $J$ on $S$ there is a unit $v \in S[\![X]\!]$ with $G.\mathrm{nthSeries}\,q = v \cdot G.\mathrm{drinfeldDivisor}\,q\,(f x_0)\,(f x_1)$.
--
--   This is the functoriality of the Drinfeld-basis condition in the Katz–Mazur sense for formal groups: a level-$q$ Drinfeld basis of a formal group pushes forward along any map of adically complete rings carrying the defining ideal into the defining ideal. It is used where Drinfeld level structures on a formal group must be followed through a base change, for instance in the identification of the maximal ideal of a universal object as the span of the two basis parameters, in the injectivity statement for the associated power-series algebra map, and in the level moduli package for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.map_of_isBaseChange
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) [IsAdicComplete I R] [IsAdicComplete J S]
    (f : R →+* S) (hf : ∀ r ∈ I, f r ∈ J) (F : FormalGroup R) (G : FormalGroup S) (h : F.IsBaseChange f G)
    (q : ℕ) (x₀ x₁ : R) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    G.IsDrinfeldBasisAdic J q (f x₀) (f x₁) := by sorry
