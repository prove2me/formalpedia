-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/bc940708-d429-538d-8281-177c88c8b475
-- title:
--   Every Drinfeld datum arises from a Deligne datum
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K$, let $\pi \in \mathcal{O}$ be irreducible, and let $B$ be a commutative $\mathcal{O}$-algebra in which the image of $\pi$ is nilpotent. Let $Q$ be a Drinfeld datum over $B$ relative to $\pi$: it consists of two assignments $x \mapsto N_0(x), N_1(x)$ of $\mathcal{O}$-submodules of $K^2$ to the points $x$ of $\operatorname{Spec} B$, each value a full lattice (finitely generated and spanning $K^2$ over $K$), with $N_0(x) \le N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$, such that for every $v \in K^2$ the loci $\{x : v \in N_i(x)\}$ are open; invertible $B$-modules $T_0, T_1$ with $B$-linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ satisfying $\Pi_1 \Pi_0 = \pi$ and $\Pi_0 \Pi_1 = \pi$; and, for each $x$, maps $u_i(x) : B_x \otimes_{\mathcal{O}} N_i(x) \to (T_i)_x$ over the local ring $B_x = \mathcal{O}_{\operatorname{Spec} B, x}$ that are compatible with the inclusion $N_0(x) \subseteq N_1(x)$ via $\Pi_0$ and with multiplication by $\pi$ via $\Pi_1$, together with the remaining conditions of the structure, summarised here. The conclusion asserts the existence of a Deligne datum $d$ over $B$ — an assignment, to every full lattice $M \subset K^2$, of a $B$-submodule $d.\mathrm{line}(M) \subseteq B \otimes_{\mathcal{O}} M$ with invertible quotient, monotone under inclusions of lattices, compatible with scalar homotheties, and non-degenerate at every prime of $B$ — of which $Q$ is the associated quadruple: for every $x \in \operatorname{Spec} B$, writing $L_0(x), L_1(x)$ for the full lattices $N_0(x), N_1(x)$ attached to $x$ by $Q$, the pair $(L_0(x), L_1(x))$ satisfies the edge non-degeneracy condition for $d$ at the prime of $x$ (namely $L_0(x) \le L_1(x)$, $\pi L_1(x) \subseteq L_0(x)$, and for $v \in L_1(x) \setminus L_0(x)$ one has $1 \otimes v \notin d.\mathrm{line}(L_1(x)) + \mathfrak{p}\,(B \otimes L_1(x))$, while for $v' \in L_0(x)$ not of the form $\pi w$ with $w \in L_1(x)$ one has $1 \otimes v' \notin d.\mathrm{line}(L_0(x)) + \mathfrak{p}\,(B \otimes L_0(x))$), and the kernels of $u_0(x)$ and $u_1(x)$ coincide with the lines at $L_0(x)$ and $L_1(x)$ of the Deligne datum obtained from $d$ by base change along $B \to B_x$.
--
--   This is the surjectivity half of Drinfeld's representability statement that the functor of quadruples over $\mathcal{O}$-algebras in which $\pi$ is nilpotent is represented by the formal upper half plane, in the form of Boutot–Carayol I, Prop. 5.2. Combined with the corresponding uniqueness statement it yields the bijection between Drinfeld data and points of the formal upper half plane, and it is used in the construction of period values for rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) : ∃ d : DeligneDatum (K := K) π B, Q.IsQuadrupleOf d := by sorry
