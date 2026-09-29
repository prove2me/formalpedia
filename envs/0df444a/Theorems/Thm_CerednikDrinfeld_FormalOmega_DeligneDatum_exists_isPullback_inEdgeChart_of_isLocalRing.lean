-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/633e557b-0b85-52b0-a116-8afcea83e450
-- title:
--   Pull-back of a Deligne datum into the standard edge chart
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K$, let $\pi\in\mathcal O$ be irreducible, and let $g\in \mathrm{GL}_2(K)$ have underlying matrix $\operatorname{diag}(\pi,1)$. Let $B$ be a commutative local $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, and let $d$ be a Deligne datum over $B$, that is: an assignment to each full lattice $M\subseteq K^2$ of a $B$-submodule $d.\mathrm{line}(M)\subseteq B\otimes_{\mathcal O}M$ with invertible quotient, compatible with inclusions of lattices (the image of $d.\mathrm{line}(M')$ lands in $d.\mathrm{line}(M)$ when $M'\subseteq M$), equivariant for scalar homotheties, and nondegenerate at every prime ideal of $B$. Then there exist $h\in \mathrm{GL}_2(K)$ and a Deligne datum $d'$ over $B$ such that, first, $d'$ is the pull-back of $d$ along $h$: for every full lattice $M$, $d'.\mathrm{line}(M)$ is the preimage of $d.\mathrm{line}(hM)$ under the base-changed isomorphism $B\otimes_{\mathcal O}M\cong B\otimes_{\mathcal O}hM$; and, second, $d'$ lies in the edge chart of the pair $(gL_0,L_0)$, $L_0=\mathcal O^2$, meaning that for every prime ideal $\mathfrak p$ of $B$ one has $gL_0\subseteq L_0$, $\pi L_0\subseteq gL_0$, for $v\in L_0\setminus gL_0$ the element $1\otimes v$ lies outside $d'.\mathrm{line}(L_0)+\mathfrak p\,(B\otimes_{\mathcal O}L_0)$, and for $v'\in gL_0$ not of the form $\pi w$ with $w\in L_0$ the element $1\otimes v'$ lies outside $d'.\mathrm{line}(gL_0)+\mathfrak p\,(B\otimes_{\mathcal O}gL_0)$.
--
--   This is the statement that the $\mathrm{GL}_2(K)$-translates of the standard edge chart cover Drinfeld's formal upper half plane, in the Deligne-datum (line-in-a-lattice) model: every point over a local base is, after a change of lattice basis, a point of the chart attached to the standard edge $(\pi$-neighbouring pair $\mathcal O^2\supset g\mathcal O^2)$ of the Bruhat–Tits tree. It is used to produce finite coverings by edge charts over finite bases, to realise the functor of $\pi$-nilpotent points by a scheme with open chart immersions, and in the uniformisation statement for the associated quaternionic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K) (d' : DeligneDatum (K := K) π B),
      DeligneDatum.IsPullback (K := K) (π := π) B h d d' ∧
      d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by sorry
