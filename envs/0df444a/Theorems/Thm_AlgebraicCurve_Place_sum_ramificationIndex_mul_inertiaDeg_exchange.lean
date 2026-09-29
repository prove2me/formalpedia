-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange
-- name    : AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e6f00284-f09d-527a-be0a-e8a397b38693
-- title:
--   Local exchange identity for places in a linearly disjoint compositum
-- statement:
--   Let $K$ be a field and $F$, $F_1$, $F_2$, $E$ fields forming a tower of $K$-algebras with $F_1$, $F_2$, $E$ extensions of $F$ and $E$ an extension of both $F_1$ and $F_2$, all the relevant scalar-tower compatibilities holding, with $E/F$, $F_1/F$, $F_2/F$, $E/F_1$, $E/F_2$ finite and $E/F$ separable. Assume $E$ is generated over $F$ by the images of $F_1$ and $F_2$, i.e. $\mathrm{adjoin}_F$ of the union of the two ranges is all of $E$ (`hgen`), and that $[E:F] = [F_1:F]\,[F_2:F]$ (`hLD`, linear disjointness). Here a place of a $K$-algebra $L$ is a valuation subring of $L$ containing the image of $K$, different from $L$, and a principal ideal ring; restriction of a place is its preimage valuation subring, the ramification index over a subfield is the least positive value of the valuation on nonzero elements of that subfield, and the inertia degree is the degree of the residue field over the residue field of the restriction. Given places $w_1$ of $F_1$ and $w_2$ of $F_2$ both restricting to $v$ on $F$, and a finset $T$ of places of $E$ consisting exactly of those $W$ with $W|_{F_1} = w_1$ and $W|_{F_2} = w_2$, the conclusion is $\sum_{W \in T} e(W/w_1)\, f(W/w_2) = f(w_1/v)\, e(w_2/v)$.
--
--   This is the place-by-place form of the identity "push–pull equals pull–push" for divisors in a linearly disjoint compositum of function fields: the left-hand side is the coefficient of $w_2$ obtained by pushing $w_1$ forward to $F$ and pulling back to $F_2$, computed instead by pulling $w_1$ back to $E$ and pushing forward to $F_2$. It is used in the proof of the commutation of pullback and pushforward for divisors, [`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`](thm.html#AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong), and is deduced from the bi-fibre counting identity together with the multiplicativity of ramification indices and inertia degrees in towers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Mathlib.FieldTheory.Separable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E] [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E] [IsScalarTower F F₂ E] [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E] (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤) (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂) (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v) (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) : ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ = w₁.inertiaDeg F * w₂.ramificationIndex F := by sorry
