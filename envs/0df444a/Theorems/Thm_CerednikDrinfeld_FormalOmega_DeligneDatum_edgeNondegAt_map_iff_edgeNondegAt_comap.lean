-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_map_iff_edgeNondegAt_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/bc5aaf4b-4573-5fd2-8e79-2162e7801ea6
-- title:
--   Edge nondegeneracy of a Deligne datum under base change
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field with an $\mathcal O$-algebra structure, and $\pi \in \mathcal O$; let $B$ and $B'$ be commutative $\mathcal O$-algebras and $f \colon B \to B'$ an $\mathcal O$-algebra homomorphism. Let $d$ be a Deligne datum over $B$ for the data $(\pi, K)$, that is, a family of $B$-submodules $d.\mathrm{line}\,L \subseteq B \otimes_{\mathcal O} L$ indexed by the full lattices $L \subseteq K^2$ (finitely generated $\mathcal O$-submodules spanning $K^2$ over $K$), with invertible quotients and the monotonicity, homothety and nondegeneracy conditions. Let $\mathfrak q$ be a prime ideal of $B'$ and let $M', M$ be full lattices. The assertion is that the base-changed datum `d.map π f`, whose line at $L$ is the $B'$-span of the image of $d.\mathrm{line}\,L$ under $f \otimes \mathrm{id}_L$, satisfies the edge condition at $\mathfrak q$ for the pair $(M', M)$ if and only if $d$ satisfies it at $f^{-1}(\mathfrak q)$. Here the edge condition `EdgeNondegAt` at a prime $\mathfrak p$ for $(M', M)$ is the conjunction of: $M' \subseteq M$; $\pi v \in M'$ for every $v \in M$; for every $v \in M$ with $v \notin M'$, the element $1 \otimes v$ does not lie in $d.\mathrm{line}\,M + \mathfrak p \cdot (B \otimes_{\mathcal O} M)$; and for every $v' \in M'$ not of the form $\pi w$ with $w \in M$, the element $1 \otimes v'$ does not lie in $d.\mathrm{line}\,M' + \mathfrak p \cdot (B \otimes_{\mathcal O} M')$.
--
--   This is the compatibility with base change of Deligne's edge (nondegeneracy) condition, in the kernel formulation of the functor represented by the formal Drinfeld upper half plane: the condition localised at a prime of $B'$ is detected on the original datum at the contracted prime. It is used in the identification of the edge charts of the formal model, and in the representability and admissibility statements for $\widehat\Omega$ and for the moduli package attached to it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_map_iff_edgeNondegAt_comap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B) (𝔮 : Ideal B') [𝔮.IsPrime] (M' M : FullLattice 𝒪 K) :
    (d.map π f).EdgeNondegAt π 𝔮 M' M ↔ d.EdgeNondegAt π (𝔮.comap f) M' M := by sorry
