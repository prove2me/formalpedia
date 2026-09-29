-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc
-- name    : AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/4ef37a0a-76d3-5731-8061-0eff00fa2b50
-- title:
--   Divisibility of Pic⁰ for function fields over K(X)
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $L'$ be a field carrying both a $K$-algebra structure and a $\mathrm{RatFunc}\,K$-algebra structure, the two being compatible in the sense of a scalar tower $K \subseteq \mathrm{RatFunc}\,K \subseteq L'$, and assume $L'$ is finite-dimensional over the rational function field $\mathrm{RatFunc}\,K$. Here $\mathrm{Pic0}\,K\,L'$ denotes the quotient of the group of degree-zero divisors of $L'/K$ — finitely supported functions from the places of $L'/K$ to $\mathbb{Z}$ lying in the kernel of the degree map — by the subgroup of those degree-zero divisors that are principal, i.e. of the form $v \mapsto \mathrm{ord}_v(f)$ for some nonzero $f \in L'$. The assertion is that this group is divisible by every nonzero integer: for every integer $n \neq 0$ and every class $x \in \mathrm{Pic0}\,K\,L'$ there exists $y \in \mathrm{Pic0}\,K\,L'$ with $n \cdot y = x$.
--
--   This is the surjectivity of multiplication by $n$ on the Jacobian of a smooth projective curve over an algebraically closed field of characteristic zero, expressed for the degree-zero divisor class group of a one-variable function field presented as a finite extension of $K(X)$. In this form it is the divisibility input to the non-degeneracy of the divisorial Weil pairing on $\mathrm{Pic}^0[n]$ and to the construction of pairings on torsion of modular curves compatible with the Galois and Hecke actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc.{u, v}
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
    [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'] :
    ∀ n : ℤ, n ≠ 0 → ∀ x : Pic0 K L', ∃ y : Pic0 K L', n • y = x := by sorry
