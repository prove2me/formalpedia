-- Prove2me | Theorems.Thm_AlgebraicCurve_natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue
-- name    : AlgebraicCurve.natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/bb54145d-ef42-59e5-be58-4c68cbbbd144
-- title:
--   Dimension bound for function pairs with matched residues
-- statement:
--   Let $k$ and $F$ be fields with $F$ a $k$-algebra, where a place of $F/k$ is a valuation subring of $F$ containing the image of $k$, proper in $F$, and a principal ideal ring, the degree of a place being the $k$-dimension of its residue field, a divisor being a finitely supported function from places to $\mathbb{Z}$ with $\deg D = \sum_v D(v)\,\deg v$, and $\mathrm{LSpace}(D) = \{f \in F : v(f) \le \exp(D(v)) \text{ for all } v\}$ with $\ell(D)$ its $k$-dimension and $g = \mathrm{genusFF}\,k\,F$ the $k$-dimension of $H^1(0)$. Assume every place has degree $1$; every $\mathrm{LSpace}(D)$ is finite-dimensional over $k$; and $\ell(D) = \deg D + 1 - g$ whenever $2g - 1 \le \deg D$. Let $W$ be a finite set of places and $NP$ a set of ordered pairs of places such that each $w \in W$ is the first coordinate of some pair in $NP$. Let $D_1, D_2$ be divisors with $D_1(w) = 0$ for all $w \in W$, $2g - 1 + \#W \le \deg D_1$ and $2g - 1 \le \deg D_2$. Let $x : \mathrm{Fin}\,m \to F \times F$ be $k$-linearly independent such that for each $a$ and each place $v$, either $(x_a)_1 = 0$ or $-D_1(v) \le \mathrm{ord}_v (x_a)_1$, and likewise either $(x_a)_2 = 0$ or $-D_2(v) \le \mathrm{ord}_v (x_a)_2$; and for each $a$ and each pair $(v, v') \in NP$ there is $c \in k$ with $(x_a)_1$ lying in the valuation ring of $v$ with residue the image of $c$, and $(x_a)_2$ lying in the valuation ring of $v'$ with residue the image of $c$. Then $m \le \deg D_1 + \deg D_2 + 2 - 2g - \#W$ as integers.
--
--   This is a Riemann–Roch dimension count for pairs of functions, each with poles bounded by one of two divisors, which are required to take a common constant value at each of a prescribed set of pairs of places; the gain of $\#W$ over the naive bound $\ell(D_1) + \ell(D_2)$ comes from the matching conditions at the places of $W$. It supplies the dimension estimate for the existence of common units in the prolongation arguments of [`ModularCurve.JHPlaceSpecialization`](def/ModularCurve_JHPlaceSpecialization.html#L52), where the two factors correspond to the two components glued along the pairs in $NP$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (hdeg : ∀ v : Place k F, v.deg = 1)
    (hfin : ∀ D : Divisor k F, FiniteDimensional k ↥(LSpace D))
    (hRR : ∀ D : Divisor k F, 2 * (genusFF k F : ℤ) - 1 ≤ D.degree → (ell D : ℤ) = D.degree + 1 - genusFF k F)
    (W : Finset (Place k F)) (NP : Set (Place k F × Place k F))
    (hNP : ∀ w ∈ W, ∃ v' : Place k F, (w, v') ∈ NP)
    (D₁ D₂ : Divisor k F) (hD₁ : ∀ w ∈ W, D₁ w = 0)
    (hdeg₁ : 2 * (genusFF k F : ℤ) - 1 + W.card ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF k F : ℤ) - 1 ≤ D₂.degree)
    {m : ℕ} (x : Fin m → F × F)
    (hx₁ : ∀ a, ∀ v : Place k F, (x a).1 = 0 ∨ -D₁ v ≤ v.ord (x a).1)
    (hx₂ : ∀ a, ∀ v : Place k F, (x a).2 = 0 ∨ -D₂ v ≤ v.ord (x a).2)
    (hxNP : ∀ a, ∀ nd ∈ NP, ∃ c : k, nd.1.HasValue (x a).1 c ∧ nd.2.HasValue (x a).2 c)
    (hli : LinearIndependent k x) :
    (m : ℤ) ≤ D₁.degree + D₂.degree + 2 - 2 * (genusFF k F : ℤ) - W.card := by sorry
