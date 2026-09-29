-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_iff_of_isBaseChange_of_isLocalHom
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_iff_of_isBaseChange_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/f93bd67e-5f20-5d4b-8de1-8ad9584633be
-- title:
--   Edge-chart membership is insensitive to local base change
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field that is an $\mathcal O$-algebra, and $\pi\in\mathcal O$. Let $B$ and $B'$ be commutative local $\mathcal O$-algebras and $f:B\to B'$ an $\mathcal O$-algebra map that is a local homomorphism. Let $d$ be a Deligne datum over $B$ and $d'$ one over $B'$: such a datum assigns to every full lattice $M\subset K^2$ (a finitely generated $\mathcal O$-submodule spanning $K^2$ over $K$) a submodule $\mathrm{line}(M)\subseteq B\otimes_{\mathcal O}M$ with invertible quotient, compatibly with inclusions of lattices and with the homothety action of $K^\times$, and nondegenerate at every prime. Assume $d'$ is the base change of $d$ along $f$, i.e. for every full lattice $M$ the submodule $d'.\mathrm{line}(M)$ is the $B'$-span of the image of $d.\mathrm{line}(M)$ under $f\otimes\mathrm{id}_M$. Then for any two full lattices $M',M$, the datum $d'$ lies in the edge chart at $(M',M)$ if and only if $d$ does: that is, for every prime $\mathfrak p'$ of $B'$ one has $M'\le M$, $\pi M\subseteq M'$, $1\otimes v\notin d'.\mathrm{line}(M)+\mathfrak p'\cdot(B'\otimes M)$ for all $v\in M\setminus M'$, and $1\otimes v'\notin d'.\mathrm{line}(M')+\mathfrak p'\cdot(B'\otimes M')$ for all $v'\in M'$ not of the form $\pi w$ with $w\in M$, precisely when the corresponding four conditions hold for $d$ at every prime $\mathfrak p$ of $B$.
--
--   This is the openness of the edge charts covering Drinfeld's formal upper half plane, in the Deligne (kernel-line) model: over a local base, whether a point lies in the chart indexed by an edge $(M',M)$ of the Bruhat–Tits tree is detected after any local base change, for instance on the residue field. It is used in the identification of the moduli functor with $\hat\Omega$ ([`CerednikDrinfeld.FormalOmega.Omega.bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart`](thm.html#CerednikDrinfeld.FormalOmega.Omega.bijective_of_algFunctor_of_forall_existsUnique_lift_of_forall_bijective_of_forall_represents_inEdgeChart)) and in the verification of the edge condition for fake elliptic curves and for the special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_iff_of_isBaseChange_of_isLocalHom.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_iff_of_isBaseChange_of_isLocalHom
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] [IsLocalRing B'] (f : B →ₐ[𝒪] B') [IsLocalHom f]
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B')
    (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) f d d') (M' M : FullLattice 𝒪 K) :
    d'.InEdgeChart π M' M ↔ d.InEdgeChart π M' M := by sorry
