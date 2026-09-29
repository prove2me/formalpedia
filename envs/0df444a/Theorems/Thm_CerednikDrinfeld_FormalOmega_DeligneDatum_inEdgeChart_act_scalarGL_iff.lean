-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/1747cd08-e91c-5f3b-973e-481a3c207dff
-- title:
--   Homothety invariance of the edge-chart condition
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field that is an $\mathcal{O}$-algebra, $\pi$ an element of $\mathcal{O}$, and $B$ a commutative $\mathcal{O}$-algebra. Let $d$ be a Deligne datum for $\pi$ over $B$: an assignment to each full $\mathcal{O}$-lattice $M \subseteq K^2$ of a $B$-submodule $d.\mathrm{line}\,M$ of $B \otimes_{\mathcal{O}} M$ with invertible quotient, monotone along inclusions of lattices after base change, compatible with homothety in the sense that $d.\mathrm{line}(cM)$ is the image of $d.\mathrm{line}\,M$ under the base change of the isomorphism $M \cong cM$, and satisfying the nondegeneracy clause at every prime of $B$. Let $M', M$ be full lattices and $c \in K^\times$, and write $cM$ for the image of $M$ under the scalar matrix $c \cdot 1 \in \mathrm{GL}_2(K)$. The assertion is that `d.InEdgeChart` holds for the pair $(cM', cM)$ if and only if it holds for $(M', M)$; here `d.InEdgeChart` at a pair $(M', M)$ means that for every prime ideal $\mathfrak{p}$ of $B$ one has $M' \subseteq M$, $\pi M \subseteq M'$, every $v \in M \setminus M'$ has $1 \otimes v \notin d.\mathrm{line}\,M + \mathfrak{p}\,(B \otimes_{\mathcal{O}} M)$, and every $v' \in M'$ not of the form $\pi w$ with $w \in M$ has $1 \otimes v' \notin d.\mathrm{line}\,M' + \mathfrak{p}\,(B \otimes_{\mathcal{O}} M')$.
--
--   This records that the edge condition defining the standard charts of the formal upper half plane depends only on the homothety classes of the two lattices, so that it is a condition on the corresponding edge of the Bruhat–Tits tree rather than on chosen representatives. It is used when passing between lattice representatives, in particular by the construction of a finite cover of the functor by edge charts and by the variant for $c^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_iff
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (c : Kˣ) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M') (FullLattice.act (scalarGL c) M) ↔ d.InEdgeChart π M' M := by sorry
