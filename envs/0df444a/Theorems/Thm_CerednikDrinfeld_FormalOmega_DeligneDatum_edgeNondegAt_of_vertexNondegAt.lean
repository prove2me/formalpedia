-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_of_vertexNondegAt
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_of_vertexNondegAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/09cae338-44e0-5c7d-ac25-8278fca63957
-- title:
--   Vertex nondegeneracy implies edge nondegeneracy at adjacent lattices
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field that is an $\mathcal O$-algebra, $\pi \in \mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $d$ be a Deligne datum for $\pi$ over $B$: it assigns to every full lattice $M$ (a finitely generated $\mathcal O$-submodule of $K^2$ spanning $K^2$ over $K$) a $B$-submodule $d.\mathrm{line}\,M$ of $B \otimes_{\mathcal O} M$ with invertible quotient, compatibly with inclusions of lattices and with homotheties, and satisfying a nondegeneracy condition at every prime of $B$. Let $\mathfrak p$ be an ideal of $B$ (primality is not assumed) and let $M', M$ be full lattices with $M' \le M$ and with $\pi v \in M'$ for all $v \in M$ (the image of $\pi$ under $\mathcal O \to K$ acting on $K^2$). Assume vertex nondegeneracy at $M$: for every $v \in M$ that is not of the form $\pi w$ with $w \in M$, the element $1 \otimes v$ does not lie in $d.\mathrm{line}\,M + \mathfrak p\,(B \otimes_{\mathcal O} M)$. Then edge nondegeneracy holds at $(M', M)$ for $\mathfrak p$, i.e. the conjunction of: $M' \le M$; $\pi M \subseteq M'$; for every $v \in M$ with $v \notin M'$, $1 \otimes v \notin d.\mathrm{line}\,M + \mathfrak p\,(B \otimes_{\mathcal O} M)$; and for every $v' \in M'$ not of the form $\pi w$ with $w \in M$, $1 \otimes v' \notin d.\mathrm{line}\,M' + \mathfrak p\,(B \otimes_{\mathcal O} M')$.
--
--   This is the passage from Deligne's nondegeneracy condition at a vertex of the Bruhat–Tits tree to the corresponding condition along any edge-pair $\pi M \subseteq M' \subseteq M$ incident to it; the degenerate pairs $M' = M$ and $M' = \pi M$ are permitted, one clause then being vacuous. It is used in the construction of the charts of the formal upper half plane, in particular by the results producing pullback squares on edge charts and the dichotomy between standard vertices and units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_of_vertexNondegAt.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_of_vertexNondegAt
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M' M : FullLattice 𝒪 K)
    (hle : M'.1 ≤ M.1) (hπM : ∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1)
    (hV : d.VertexNondegAt π 𝔭 M) :
    d.EdgeNondegAt π 𝔭 M' M := by sorry
