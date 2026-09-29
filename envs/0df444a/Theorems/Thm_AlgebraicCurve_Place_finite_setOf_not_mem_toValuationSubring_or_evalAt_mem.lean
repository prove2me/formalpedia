-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
-- name    : AlgebraicCurve.Place.finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/63578a84-6aed-55be-a510-249964e72bf6
-- title:
--   Finiteness of poles and of places with prescribed values
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `HasPrincipalDivisors K F`, i.e. every nonzero $f \in F$ admits a finitely supported function $D$ from the places of $F/K$ to $\mathbb{Z}$ with $D(v) = v.\mathrm{ord}(f)$ at every place and with $\deg D = 0$; here a place is a valuation subring $\mathcal{O}_v \subseteq F$ containing $\mathrm{algebraMap}\,K\,F$ of all of $K$, distinct from $F$ itself, and a principal ideal ring. Assume further that every place $v$ is rational, in the sense that $K \to \mathcal{O}_v/\mathfrak{m}_v$ is surjective. Let $x \in F$ lie outside the image of $\mathrm{algebraMap}\,K\,F$, and let $T$ be a finite subset of $K$. Then the set of places $v$ of $F/K$ such that either $x \notin \mathcal{O}_v$, or $v.\mathrm{evalAt}\,x \in T$, is finite, where $v.\mathrm{evalAt}\,x$ is the unique $t \in K$ whose image is the residue class of $x$ when $x \in \mathcal{O}_v$ (chosen by an inverse of the surjection $K \to \mathcal{O}_v/\mathfrak{m}_v$), and is $0$ otherwise.
--
--   This is the standard function-field fact that a non-constant function on a curve has finitely many poles and takes any prescribed finite set of values at only finitely many places. It is used in the comparison of kernels of product maps of places and, in the analysis of the modular curve $X_1(p)$, to exclude a finite set of $j$-values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hrat : ∀ v : Place K F, v.IsRational)
    (x : F) (hx : x ∉ Set.range (algebraMap K F)) (T : Finset K) :
    {v : Place K F | x ∉ v.toValuationSubring ∨ v.evalAt x ∈ (T : Set K)}.Finite := by sorry
