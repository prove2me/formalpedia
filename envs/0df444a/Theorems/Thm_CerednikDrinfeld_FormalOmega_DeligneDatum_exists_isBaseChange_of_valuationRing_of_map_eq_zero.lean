-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/d4fc1c52-650f-5338-b2fa-bad46f3b3a90
-- title:
--   Deligne data over Frac V descend to V
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain, with field of fractions $K$, and let $\pi \in \mathcal O$ be irreducible. Let $V$ be a domain which is a valuation ring and an $\mathcal O$-algebra such that the structure map sends $\pi$ to $0$, and let $L$ be a field which is an $\mathcal O$-algebra and a $V$-algebra compatibly (scalar tower) and is the field of fractions of $V$. A Deligne datum over a commutative $\mathcal O$-algebra $B$ consists of a $B$-submodule $\mathrm{line}\,M \subseteq B \otimes_{\mathcal O} M$ for every full $\mathcal O$-lattice $M \subseteq K^2$, such that each quotient $(B \otimes_{\mathcal O} M)/\mathrm{line}\,M$ is an invertible $B$-module; the lines are monotone, in that for $M' \subseteq M$ the image of $\mathrm{line}\,M'$ under the base-changed inclusion lies in $\mathrm{line}\,M$; they are homothety-equivariant, $\mathrm{line}(\mathrm{scalarGL}(c) \cdot M)$ being the image of $\mathrm{line}\,M$ under the base change of the action of the scalar matrix $c \in K^\times$; and for every prime ideal $\mathfrak p$ of $B$ there are lattices $M' \subseteq M$ with $\pi M \subseteq M'$ such that $1 \otimes v \notin \mathrm{line}\,M + \mathfrak p\,(B \otimes_{\mathcal O} M)$ for every $v \in M \setminus M'$, and $1 \otimes v' \notin \mathrm{line}\,M' + \mathfrak p\,(B \otimes_{\mathcal O} M')$ for every $v' \in M'$ not of the form $\pi w$ with $w \in M$. The assertion is that for every Deligne datum $d$ over $L$ there is a Deligne datum $d_0$ over $V$ with $d_0$ base-changing to $d$ along the canonical map $V \to L$, meaning that for every full lattice $M$ the submodule $d.\mathrm{line}\,M$ is the $L$-span of the image of $d_0.\mathrm{line}\,M$ under $\mathrm{id}_L \otimes$-type extension of scalars $V \otimes_{\mathcal O} M \to L \otimes_{\mathcal O} M$.
--
--   This is the valuative criterion input for Drinfeld's formal upper half plane on the special fibre: points of the functor of Deligne data over the fraction field of a valuation ring killed by $\pi$ lift to the valuation ring itself. It is used in the proof of [`CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing), which feeds the properness and local structure statements for the Mumford-style glueing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) :
    ∃ d₀ : DeligneDatum (K := K) π V,
      DeligneDatum.IsBaseChange (K := K) (π := π) (IsScalarTower.toAlgHom 𝒪 V L) d₀ d := by sorry
