-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_fg_forall_lineBaseChange_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/305e0157-9ac8-5819-9f05-72a60f596fd3
-- title:
--   Finitely generated model for the kernel lines near a point
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K$, let $\pi \in \mathcal{O}$ be irreducible, and let $B$ be a commutative $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent. Let $Q$ be a Drinfeld datum over $B$ relative to $\pi$ and $K$, let $x$ be a point of $\operatorname{Spec} B$, and let $L$ be a full lattice in $K^2$, i.e. a finitely generated $\mathcal{O}$-submodule of $K^2$ whose $K$-span is everything. Then there are an element $r \in B$ outside the prime of $x$ and a finitely generated $B$-submodule $N$ of $B \otimes_{\mathcal{O}} L$ with the following property: for every point $y$ of $\operatorname{Spec} B$ with $r$ outside the prime of $y$, and for every Deligne datum $d_y$ over the local ring `locRing B y` $= B_y$ (an assignment $M \mapsto d_y.\mathrm{line}\,M \subseteq B_y \otimes_{\mathcal{O}} M$ of submodules with invertible quotient, compatible with lattice inclusions, equivariant for scalar homotheties, and nondegenerate at every prime of $B_y$) such that $\ker(Q.u_0(y)) = d_y.\mathrm{line}(Q.L_0(y))$ and $\ker(Q.u_1(y)) = d_y.\mathrm{line}(Q.L_1(y))$ — here $Q.L_0(y)$, $Q.L_1(y)$ are the full lattices attached to $y$ by $Q$, whose base changes are the domains of $Q.u_0(y)$, $Q.u_1(y)$ — and such that $d_y$ satisfies the edge condition `InEdgeChart` for the pair $(Q.L_0(y), Q.L_1(y))$ at every prime of $B_y$, one has $d_y.\mathrm{line}\,L =$ the $B_y$-span of the image of $N$ under base change along $B \to B_y$.
--
--   This is the lattice-by-lattice form of the local model for a Drinfeld datum: over a basic open neighbourhood of any point of $\operatorname{Spec} B$, the kernel lines of the stalkwise Deligne data at a fixed lattice $L$ are all induced from one finitely generated $B$-submodule of $B \otimes_{\mathcal{O}} L$. It is used in the construction of a point of the formal upper half plane out of a Drinfeld datum, via [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf), and rests on the local model `exists_deligneDatum_away_forall_map` together with the uniqueness statement `DeligneDatum.eq_of_inEdgeChart_of_line_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_fg_forall_lineBaseChange_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ N : Submodule B (latticeBaseChange 𝒪 K B L), N.FG ∧
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal → ∀ dy : DeligneDatum (K := K) π (locRing B y),
        LinearMap.ker (Q.u₀ y) = dy.line (Q.L₀ y) → LinearMap.ker (Q.u₁ y) = dy.line (Q.L₁ y) →
        dy.InEdgeChart π (Q.L₀ y) (Q.L₁ y) →
          lineBaseChange (toLocRing B y) L N = dy.line L := by sorry
