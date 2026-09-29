-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_span_eq_top_forall_inEdgeChart_map_away
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_span_eq_top_forall_inEdgeChart_map_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/9bcfd127-01ce-5f03-9f3f-76b9b3cd0bfb
-- title:
--   Edge charts cover a Deligne datum on a finite basic cover
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field that is an $\mathcal{O}$-algebra, and $\pi \in \mathcal{O}$ an element whose residue ring $\mathcal{O}/(\pi)$ is finite. Let $B$ be a commutative $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent, and let $d$ be a Deligne datum for $\pi$ over $B$ relative to $K$: an assignment to every full lattice $M \subset K^2$ (a finitely generated $\mathcal{O}$-submodule spanning $K^2$ over $K$) of a $B$-submodule $d.\mathrm{line}\,M \subseteq B \otimes_{\mathcal{O}} M$ with invertible quotient, compatible with inclusions of lattices and with the homothety action of $K^\times$, and satisfying the nondegeneracy condition at some nested pair of lattices at each prime of $B$. The assertion is that there is a finite subset $s \subseteq B$ generating the unit ideal such that for each $r \in s$ there are full lattices $M' \subseteq M$ with $\pi v \in M'$ for all $v \in M$, for which: (i) for every prime ideal $\mathfrak{q}$ of $B$ not containing $r$, the predicate $\mathrm{EdgeNondegAt}$ holds, i.e. $M' \subseteq M$, $\pi M \subseteq M'$, every $v \in M \setminus M'$ has $1 \otimes v \notin d.\mathrm{line}\,M + \mathfrak{q}\,(B \otimes_{\mathcal{O}} M)$, and every $v' \in M'$ not of the form $\pi w$ with $w \in M$ has $1 \otimes v' \notin d.\mathrm{line}\,M' + \mathfrak{q}\,(B \otimes_{\mathcal{O}} M')$; and (ii) the base change of $d$ along the structure map $B \to B[1/r]$, whose lines are the $B[1/r]$-spans of the images of the lines of $d$, satisfies $\mathrm{InEdgeChart}$ for $(M', M)$, that is the same nondegeneracy condition at every prime of $B[1/r]$.
--
--   This is the openness and quasi-compactness statement for Deligne's edge condition on points of Drinfeld's formal upper half-plane in the lattice-line model: a $B$-point is shown to lie in the edge chart of a nested pair of lattices after passing to each member of a finite cover of $\operatorname{Spec} B$ by basic opens. It feeds [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq), where the pair of lattices is normalised to a standard edge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_span_eq_top_forall_inEdgeChart_map_away.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_span_eq_top_forall_inEdgeChart_map_away
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (d : DeligneDatum (K := K) π B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧ ∀ r ∈ s, ∃ (M' M : FullLattice 𝒪 K),
      M'.1 ≤ M.1 ∧ (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧
      (∀ 𝔮 : Ideal B, 𝔮.IsPrime → r ∉ 𝔮 → d.EdgeNondegAt π 𝔮 M' M) ∧
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r))).InEdgeChart π M' M := by sorry
