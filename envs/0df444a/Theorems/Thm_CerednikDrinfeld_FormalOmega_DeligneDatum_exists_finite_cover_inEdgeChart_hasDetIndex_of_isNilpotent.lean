-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/444336eb-bcc2-5e19-8da1-c66bd83ca103
-- title:
--   Finite cover putting a Deligne datum in normalised edge charts
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K$, let $\pi \in \mathcal O$ be irreducible, and assume the residue ring $\mathcal O/(\pi)$ is finite. Let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, and let $d$ be a Deligne datum over $B$ for $\pi$, i.e. a family of $B$-submodules $d.\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$, indexed by the full lattices $M$ in $K^2$ (finitely generated $\mathcal O$-submodules spanning $K^2$ over $K$), with invertible quotients, compatible with lattice inclusions, equivariant for scalar homotheties, and nondegenerate at every prime of $B$. The assertion is that there are an integer $k$, elements $f_0,\dots,f_{k-1}$ of $B$ generating the unit ideal, and families of full lattices $M'_i$, $M_i$ such that for every $i$: $M'_i \subseteq M_i$ and $\pi M_i \subseteq M'_i$; $M'_i$ has determinant index $0$ for $\pi$, meaning $M'_i = g \cdot \mathcal O^2$ for some $g \in \mathrm{GL}_2(K)$ whose determinant is the image in $K$ of a unit of $\mathcal O$; and the base change of $d$ along the structural map $B \to B[1/f_i]$ (the localisation away from $f_i$), obtained by spanning the images of the lines, lies in the edge chart of $(M'_i, M_i)$, that is, for every prime ideal $\mathfrak p$ of $B[1/f_i]$ one has $M'_i \subseteq M_i$, $\pi M_i \subseteq M'_i$, and moreover $1 \otimes v \notin \mathrm{line}(M_i) + \mathfrak p\cdot(B[1/f_i] \otimes_{\mathcal O} M_i)$ for every $v \in M_i \setminus M'_i$, and $1 \otimes v' \notin \mathrm{line}(M'_i) + \mathfrak p\cdot(B[1/f_i] \otimes_{\mathcal O} M'_i)$ for every $v' \in M'_i$ not of the form $\pi w$ with $w \in M_i$.
--
--   This is the local-charts covering statement for the functor of Deligne data on $\pi$-nilpotent algebras: every such datum becomes, after passing to a finite Zariski cover of the base, the datum attached to an oriented edge $\pi M \subseteq M' \subseteq M$ of the Bruhat–Tits tree, normalised so that the smaller lattice has determinant index $0$. It is used in the construction of a Drinfeld quadruple from a Deligne datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (k : ℕ) (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤) (M' M : Fin k → FullLattice 𝒪 K),
      ∀ i : Fin k, (M' i).1 ≤ (M i).1 ∧ (∀ v ∈ (M i).1, algebraMap 𝒪 K π • v ∈ (M' i).1) ∧ HasDetIndex π (M' i).1 0 ∧
        (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).InEdgeChart π (M' i) (M i) := by sorry
