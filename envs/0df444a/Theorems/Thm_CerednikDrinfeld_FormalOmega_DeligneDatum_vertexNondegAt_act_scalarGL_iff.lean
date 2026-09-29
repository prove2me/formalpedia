-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_vertexNondegAt_act_scalarGL_iff
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.vertexNondegAt_act_scalarGL_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/8c3cab11-1489-58a0-9ac0-9dab22cf7fed
-- title:
--   Homothety invariance of the vertex nondegeneracy condition
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi$ an element of $\mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $d$ be a Deligne datum over $B$ for $\pi$, that is, a family assigning to every full lattice $M \subset K^2$ a $B$-submodule $d.\mathrm{line}\,M$ of $B \otimes_{\mathcal O} M$ with invertible quotient, compatible with inclusions of lattices, transported to itself along the base change of the scaling isomorphisms $M \to cM$, and satisfying the nondegeneracy axiom at every prime ideal of $B$. Let $\mathfrak p$ be an ideal of $B$, let $c \in K^\times$, and let $M$ be a full lattice in $K^2$. Write $cM$ for the image of $M$ under the invertible matrix $c \cdot 1$ (the lattice `FullLattice.act (scalarGL c) M`). The assertion is that the condition `VertexNondegAt` at $\mathfrak p$ holds for $cM$ if and only if it holds for $M$, where for a lattice $L$ this condition says: for every $v \in L$ which is not of the form $\pi w$ (with $\pi$ acting through $\mathcal O \to K$) for any $w \in L$, the element $1 \otimes v$ of $B \otimes_{\mathcal O} L$ does not lie in $d.\mathrm{line}\,L + \mathfrak p \cdot (B \otimes_{\mathcal O} L)$.
--
--   This is the statement that Deligne's nondegeneracy condition at a vertex depends only on the homothety class of the lattice, i.e. on the corresponding vertex of the Bruhat–Tits tree of $\mathrm{GL}_2(K)$, rather than on the lattice itself. It is used in the comparison of Deligne data with Drinfeld quadruples, for instance in the characterisations of `IsQuadrupleOf` by the shape of the line at a vertex.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_vertexNondegAt_act_scalarGL_iff.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.vertexNondegAt_act_scalarGL_iff
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ) (M : FullLattice 𝒪 K) :
    d.VertexNondegAt π 𝔭 (FullLattice.act (scalarGL c) M) ↔ d.VertexNondegAt π 𝔭 M := by sorry
