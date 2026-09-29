-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow
-- name    : AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/25accfa7-e793-5bac-928b-9a2c89b63248
-- title:
--   Finiteness of Pic⁰[n] from prime-power torsion
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. Here a divisor is a finitely supported function from the places of $F/K$ to $\mathbb{Z}$, $\mathrm{Pic}^0$ is the quotient of the subgroup of divisors of degree zero (the kernel of the degree map) by the subgroup of divisors that are principal, i.e. of the form $v \mapsto \mathrm{ord}_v(f)$ for some $f \neq 0$, intersected with the degree-zero divisors, and for $n \in \mathbb{N}$ the $n$-torsion `Pic0.torsion K F n` is the additive subgroup underlying the $\mathbb{Z}$-submodule of elements killed by $n$. The hypothesis is that for every prime number $p$, equipped with its primality instance, and every natural number $k$, the $p^k$-torsion subgroup of $\mathrm{Pic}^0$ is finite. The conclusion is that for every natural number $n$ with $0 < n$, the $n$-torsion subgroup of $\mathrm{Pic}^0$ is finite. Only finiteness is asserted; no cardinality is computed, and no hypothesis relating $F/K$ to a curve is imposed.
--
--   This is the elementary multiplicative bookkeeping step that passes from torsion bounds at prime powers, where the classical count $\#J[p^k] = p^{2gk}$ lives, to finiteness of $\mathrm{Pic}^0[n]$ for all $n \geq 1$. It is used to obtain finiteness of torsion for divisor class groups over algebraically closed fields of characteristic zero, and in the analysis of torsion in the component and inertia-invariant subgroups attached to Néron models of modular Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Finite (Pic0.torsion K F (p ^ k))) (n : ℕ) (hn : 0 < n) :
    Finite (Pic0.torsion K F n) := by sorry
