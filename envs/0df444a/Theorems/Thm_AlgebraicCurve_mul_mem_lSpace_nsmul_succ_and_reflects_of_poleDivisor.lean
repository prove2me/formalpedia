-- Prove2me | Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
-- name    : AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/7f6b18a8-cdb4-5d61-91c5-6e018539df1e
-- title:
--   Multiplication by x on the pole filtration is graded-injective
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $x \in F$, and let $D$ be a divisor of $F/K$, i.e. a finitely supported function on the type `Place K F` of places — valuation subrings of $F$ that contain the image of $K$, are not all of $F$, and are principal ideal rings — with values in $\mathbb{Z}$. Assume that $D$ is the pole divisor of $x$, in the sense that $D(v) = \max(0, -\operatorname{ord}_v x)$ for every place $v$, where $\operatorname{ord}_v$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued valuation attached to $v$. Let $m$ be a natural number. Writing $\mathcal{L}(E) = \{f \in F : v(f) \le \exp(E(v)) \text{ for all } v\}$ for the Riemann–Roch space of a divisor $E$, a $K$-submodule of $F$, the theorem asserts two things: first, for every $g \in \mathcal{L}(m \cdot D)$ one has $x g \in \mathcal{L}((m+1) \cdot D)$; second, for every $g \in \mathcal{L}((m+1) \cdot D)$ such that also $x g \in \mathcal{L}((m+1) \cdot D)$, one already has $g \in \mathcal{L}(m \cdot D)$.
--
--   This is the pole-order arithmetic underlying the fact that multiplication by $x$ induces an injective map $\mathcal{L}(mD)/\mathcal{L}((m-1)D) \to \mathcal{L}((m+1)D)/\mathcal{L}(mD)$ on the graded pieces of the filtration by multiples of the pole divisor of $x$. It feeds the construction of bases adapted to this filtration and the associated linear independence statements, being used by [`AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ`](thm.html#AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ), [`AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq`](thm.html#AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq) and [`AlgebraicCurve.linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq`](thm.html#AlgebraicCurve.linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (m : ℕ) :
    (∀ g ∈ LSpace ((m : ℕ) • D), x * g ∈ LSpace ((m + 1) • D)) ∧
    (∀ g ∈ LSpace ((m + 1) • D), x * g ∈ LSpace ((m + 1) • D) → g ∈ LSpace (m • D)) := by sorry
