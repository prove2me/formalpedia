-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/80e1dc83-7ca9-53ad-977a-3d73ce2d71ff
-- title:
--   Edge nondegeneracy transports under pull-back by h
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi$ an element of $\mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $d$ be a Deligne datum over $B$ (a family of $B$-submodules $\mathrm{line}\,M \subseteq B\otimes_{\mathcal O} M$ indexed by the full $\mathcal O$-lattices $M \subset K^2$, with invertible quotients, compatible with lattice inclusions and with homotheties, and satisfying the nondegeneracy axiom), let $h \in \mathrm{GL}_2(K)$, let $\mathfrak p$ be an ideal of $B$ — primality is not assumed — and let $N' , N$ be full lattices. Assume $d$ satisfies `EdgeNondegAt` at $(\mathfrak p, N', N)$, that is: $N' \subseteq N$; $\pi v \in N'$ for every $v \in N$; for every $v \in N$ with $v \notin N'$ one has $1 \otimes v \notin \mathrm{line}\,N + \mathfrak p\,(B\otimes_{\mathcal O} N)$; and for every $v' \in N'$ not of the form $\pi w$ with $w \in N$ one has $1 \otimes v' \notin \mathrm{line}\,N' + \mathfrak p\,(B\otimes_{\mathcal O} N')$. Then the pulled-back datum `DeligneDatum.pullback π B h d`, whose line at a lattice $M$ is the preimage of $d.\mathrm{line}(hM)$ under the base-changed isomorphism $B\otimes_{\mathcal O} M \simeq B\otimes_{\mathcal O} hM$, satisfies `EdgeNondegAt` at $(\mathfrak p, h^{-1}N', h^{-1}N)$, where $h^{-1}N$ denotes the image of $N$ under $h^{-1}$.
--
--   This is Deligne's edge (nondegeneracy) condition for a pair of lattices at a prime of $B$, transported along the pull-back action of $\mathrm{GL}_2(K)$ on the moduli functor of Deligne data that represents Drinfeld's formal upper half-plane. It isolates, for a given pair of lattices, the computation performed inside the `nondeg` field of `DeligneDatum.pullback`, and is used to move a point into the standard edge chart after an edge-transitivity move, notably by `DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing` and in the construction of adic points of the Mumford tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (h : Matrix.GeneralLinearGroup (Fin 2) K) (𝔭 : Ideal B) (N' N : FullLattice 𝒪 K)
    (hN : d.EdgeNondegAt π 𝔭 N' N) :
    (DeligneDatum.pullback π B h d).EdgeNondegAt π 𝔭 (FullLattice.act h⁻¹ N') (FullLattice.act h⁻¹ N) := by sorry
