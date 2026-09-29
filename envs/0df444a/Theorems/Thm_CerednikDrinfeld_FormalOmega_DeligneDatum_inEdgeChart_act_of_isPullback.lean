-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/cf41dbce-eff6-5716-9957-64a8ffe9abaf
-- title:
--   Edge charts transport along the GL₂(K) pull-back of Deligne data
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field that is an $\mathcal{O}$-algebra, $\pi \in \mathcal{O}$, and $B$ a commutative $\mathcal{O}$-algebra. Let $h \in GL_2(K)$ and let $d, d'$ be Deligne data over $B$ for $(K,\pi)$, i.e. each assigns to every full $\mathcal{O}$-lattice $M \subset K^2$ a $B$-submodule $\mathrm{line}\,M \subseteq B \otimes_{\mathcal{O}} M$ with invertible quotient, compatibly with lattice inclusions and with the action of scalar matrices, and satisfying the nondegeneracy condition at every prime of $B$. Assume `DeligneDatum.IsPullback`, that is, for every full lattice $M$ one has $d'.\mathrm{line}\,M = (1 \otimes h)^{-1}\bigl(d.\mathrm{line}(hM)\bigr)$, the preimage along the base-changed isomorphism $B \otimes_{\mathcal{O}} M \cong B \otimes_{\mathcal{O}} hM$. Let $M', M$ be full lattices and assume $d'$ lies in the edge chart of $(M',M)$: for every prime ideal $\mathfrak{p}$ of $B$ one has $M' \subseteq M$, $\pi M \subseteq M'$, every $v \in M$ with $v \notin M'$ satisfies $1 \otimes v \notin d'.\mathrm{line}\,M + \mathfrak{p}(B \otimes M)$, and every $v' \in M'$ not of the form $\pi w$ with $w \in M$ satisfies $1 \otimes v' \notin d'.\mathrm{line}\,M' + \mathfrak{p}(B \otimes M')$. The conclusion is that $d$ lies in the edge chart of the translated pair $(hM', hM)$, with all four conditions holding for $d$ at every prime of $B$.
--
--   The statement records that the $GL_2(K)$-action on Deligne data for Drinfeld's formal upper half plane permutes the edge charts, sending the chart indexed by the pair of lattices $(M',M)$ to the one indexed by $(hM',hM)$. It is used where a datum known to lie in a standard edge chart after pull-back must be placed in the translated chart, for instance in the construction of finite covers by edge charts and in the representability arguments for the functor `Omega`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_of_isPullback
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (h : Matrix.GeneralLinearGroup (Fin 2) K) {d d' : DeligneDatum (K := K) π B}
    (hd : DeligneDatum.IsPullback (K := K) (π := π) B h d d')
    {M' M : FullLattice 𝒪 K} (hd' : d'.InEdgeChart π M' M) :
    d.InEdgeChart π (FullLattice.act h M') (FullLattice.act h M) := by sorry
