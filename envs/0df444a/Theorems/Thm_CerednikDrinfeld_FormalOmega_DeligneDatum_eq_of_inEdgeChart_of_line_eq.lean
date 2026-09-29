-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/d9ecc514-11ff-5cd4-b5c2-dc960d93ba01
-- title:
--   A Deligne datum in an edge chart is determined by its two lines
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain, $K$ a field which is an $\mathcal{O}$-algebra and a fraction field of $\mathcal{O}$, and $\pi \in \mathcal{O}$ an irreducible element; let $B$ be a commutative $\mathcal{O}$-algebra. A full lattice in $K^2$ means a finitely generated $\mathcal{O}$-submodule of $K^2$ whose $K$-span is all of $K^2$, and a `DeligneDatum` for $\pi$ over $B$ consists of an assignment $M \mapsto \mathrm{line}\,M$, a $B$-submodule of $B \otimes_{\mathcal{O}} M$ for each full lattice $M$, such that each quotient $(B \otimes_{\mathcal{O}} M)/\mathrm{line}\,M$ is an invertible $B$-module, such that $\mathrm{line}\,M'$ maps into $\mathrm{line}\,M$ under the base change of the inclusion whenever $M' \subseteq M$, such that $\mathrm{line}$ is compatible with the homothety action of $\mathrm{scalarGL}(c)$, $c \in K^\times$, and such that for every prime ideal $\mathfrak{p}$ of $B$ there is a nested pair of full lattices witnessing Deligne's nondegeneracy condition. Given two such data $d, d'$ and full lattices $M', M$, assume that $d$ satisfies that nondegeneracy condition at the pair $(M', M)$ for every prime $\mathfrak{p} \subseteq B$, i.e. $M' \subseteq M$, $\pi M \subseteq M'$, for every $v \in M \setminus M'$ one has $1 \otimes v \notin \mathrm{line}\,M + \mathfrak{p}\cdot(B \otimes_{\mathcal{O}} M)$, and for every $v' \in M'$ not of the form $\pi w$ with $w \in M$ one has $1 \otimes v' \notin \mathrm{line}\,M' + \mathfrak{p}\cdot(B \otimes_{\mathcal{O}} M')$. If moreover $d'.\mathrm{line}\,M = d.\mathrm{line}\,M$ and $d'.\mathrm{line}\,M' = d.\mathrm{line}\,M'$, then $d' = d$, so the two data have the same line at every full lattice.
--
--   This is the uniqueness half of the identification of the edge chart attached to a nested pair of lattices with an open subfunctor of Drinfeld's functor of all lattices: a point of the formal upper half plane lying in the chart of $(M', M)$ over an arbitrary base is determined by its pair of lines at $M$ and $M'$. It is used in the construction of the algebra map out of the edge chart ring realising a Deligne datum, in the reduction of equality of data to a finite set of lattices, and in the uniqueness statement for the Deligne datum attached to a Drinfeld datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d d' : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (h : d.InEdgeChart π M' M)
    (hM : d'.line M = d.line M) (hM' : d'.line M' = d.line M') : d' = d := by sorry
