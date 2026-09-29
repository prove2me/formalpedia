-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank
-- name    : AlgebraicCurve.Place.sum_fiber_ord_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/1f7ded8d-d3c8-558e-a002-4e7c879388ef
-- title:
--   Fibres of a transcendental function have degree [F:ℂ(x)]
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure satisfying `IsCurveOver ℂ F`, i.e. every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place $v$ is $v.\mathrm{ord}\,f$, every place of $F$ over $\mathbb{C}$ has residue field finite over $\mathbb{C}$, and the module of Kähler differentials $\Omega[F/\mathbb{C}]$ is free of rank $1$ over $F$; here a place is a valuation subring of $F$ containing the image of $\mathbb{C}$, distinct from $F$ itself, and a principal ideal ring, and $\mathrm{ord}$ is minus the logarithm of its associated adic valuation. Let $x \in F$ be transcendental over $\mathbb{C}$, with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x) = \mathrm{adjoin}\,\mathbb{C}\,\{x\}$. Two assertions are made, both with right-hand side $n = \mathrm{finrank}_{\mathbb{C}(x)} F$. First, for every $b \in \mathbb{C}$ and every finite set $s$ of places whose members are exactly the places $w$ with $x$ in the valuation subring of $w$ and $\mathrm{evalAt}\,w\,x = b$ (the element of $\mathbb{C}$ mapping to the residue of $x$), $\sum_{w \in s} (w.\mathrm{ord}(x - b))^{+} = n$. Second, for every finite set $s$ of places whose members are exactly the places $w$ with $x$ outside the valuation subring of $w$, $\sum_{w \in s} (w.\mathrm{ord}\,x^{-1})^{+} = n$. In both sums the integer orders are truncated to $\mathbb{N}$; the finite set enumerating the relevant places is hypothesised rather than produced.
--
--   This is the classical statement that, on a complex function field of one variable, the zero divisor of $x - b$ and the pole divisor of $x$ each have degree $[F:\mathbb{C}(x)]$, so that a transcendental function attains every value, and has its poles, with total multiplicity equal to that degree. It serves the grid construction on curves, being used in the existence statements [`AlgebraicCurve.exists_dissectionScaleData`](thm.html#AlgebraicCurve.exists_dissectionScaleData) and [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sum_fiber_ord_eq_finrank.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IntermediateField

theorem AlgebraicCurve.Place.sum_fiber_ord_eq_finrank {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F] :
    (∀ (b : ℂ) (s : Finset (Place ℂ F)),
      (∀ w : Place ℂ F, w ∈ s ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b) →
      ∑ w ∈ s, (w.ord (x - algebraMap ℂ F b)).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) ∧
    (∀ s : Finset (Place ℂ F), (∀ w : Place ℂ F, w ∈ s ↔ x ∉ w.toValuationSubring) →
      ∑ w ∈ s, (w.ord x⁻¹).toNat = Module.finrank (↥(adjoin ℂ ({x} : Set F))) F) := by sorry
