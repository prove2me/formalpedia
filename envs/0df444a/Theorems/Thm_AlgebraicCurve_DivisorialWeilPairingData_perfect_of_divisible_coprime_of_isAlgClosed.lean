-- Prove2me | Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_perfect_of_divisible_coprime_of_isAlgClosed
-- name    : AlgebraicCurve.DivisorialWeilPairingData.perfect_of_divisible_coprime_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/3874b7d6-abb7-50c3-a513-8fb481d44ec8
-- title:
--   Perfectness of a divisorial Weil pairing on Pic⁰[n]
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field that is an algebra over $K$ and over the rational function field $\mathrm{RatFunc}\,K$, compatibly (scalar tower), and finite-dimensional over $\mathrm{RatFunc}\,K$; assume `HasPrincipalDivisors K F`, i.e. every nonzero $f \in F$ has an associated divisor, a finitely supported integer-valued function $D$ on the places of $F/K$ with $D(v) = \mathrm{ord}_v(f)$ for all $v$ and $\deg D = 0$. Let $n$ be a nonzero natural number with $n \neq 0$ in $K$. Assume the divisibility hypothesis `hdiv`: for every field $L'$ in the same universe as $F$, equipped with the same kind of structure ($K$- and $\mathrm{RatFunc}\,K$-algebra, scalar tower, finite over $\mathrm{RatFunc}\,K$), and every integer $m$ with $m \neq 0$ in $K$, multiplication by $m$ on $\mathrm{Pic}^0 = \{\text{degree-zero divisors}\}/\{\text{principal divisors}\}$ of $L'$ is surjective. Assume further that the $n$-torsion subgroup $\mathrm{Pic}^0(F/K)[n]$ is finite, and let $e$ be a `DivisorialWeilPairingData K F n`, that is: a pairing $\mathrm{Pic}^0[n] \times \mathrm{Pic}^0[n] \to K$ which agrees with the pairing attached to every Weil datum on the pair of classes that datum determines, together with a moving property (every $n$-torsion class is represented by a degree-zero divisor supported at rational places avoiding any prescribed finite set of places). Then $e$ is perfect: the additive map $e.\mathrm{toHom}$, sending $x$ to the character $e(x, \cdot)$ in `HomPic0Gm K F n`, is bijective.
--
--   This is the nondegeneracy (perfect self-duality) statement for the Weil pairing on the $n$-torsion of the degree-zero divisor class group of a function field, here in the form where $n$ is only assumed prime to the characteristic rather than $K$ of characteristic zero. It feeds the autoduality of the Jacobian used downstream, and is cited in the finiteness statement [`ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_DivisorialWeilPairingData_perfect_of_divisible_coprime_of_isAlgClosed.lean

import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.DivisorialWeilPairingData.perfect_of_divisible_coprime_of_isAlgClosed.{u, v} {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] {n : ℕ} [NeZero n] (hn : (n : K) ≠ 0)

    (hdiv : ∀ (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
      [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
      ∀ (m : ℤ), (m : K) ≠ 0 → ∀ x : Pic0 K L', ∃ y, m • y = x)
    [Finite (Pic0.torsion K F n)]
    (e : DivisorialWeilPairingData K F n) : e.Perfect := by sorry
