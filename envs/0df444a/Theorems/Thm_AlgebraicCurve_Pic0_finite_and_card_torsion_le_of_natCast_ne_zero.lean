-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_finite_and_card_torsion_le_of_natCast_ne_zero
-- name    : AlgebraicCurve.Pic0.finite_and_card_torsion_le_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f11ccc90-b834-5918-b9be-789d6fb23811
-- title:
--   Finiteness and n^{2g} bound for n-torsion of Pic⁰
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ algebraically closed, and assume $F$ is a function field in one variable over $K$ in the sense that some $x \in F$ is transcendental over $K$ and $F$ is finite-dimensional over the intermediate field $K(x)$. Assume further that $F/K$ is a curve in the project's sense: every nonzero $f \in F$ has a (finitely supported) divisor whose value at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$, every place $v$ of $F/K$ has residue field finite over $K$, and the module of Kähler differentials $\Omega_{F/K}$ is free of rank $1$ over $F$. Let $n$ be a natural number with $n \neq 0$ and with $n \neq 0$ in $K$. Then the group of $n$-torsion elements of $\mathrm{Pic}^0(F/K)$ — that is, the subtype of classes $c$ in the quotient of the degree-zero divisors (finitely supported $\mathbb{Z}$-valued functions on places of $F/K$ with total degree $0$) by the subgroup of principal divisors, satisfying $n \cdot c = 0$ — is finite, and its cardinality is at most $n^{2g}$, where $g = \mathrm{genusFF}\,K\,F$ is the $K$-dimension of $H^1$ of the zero divisor.
--
--   This is the inequality half, together with finiteness, of the classical count $\#\mathrm{Pic}^0(F/K)[n] = n^{2g}$ for $n$ prime to the characteristic, stated uniformly in the characteristic of the algebraically closed base field. It feeds the reduction and Abel–Jacobi counting arguments for $\mathrm{Pic}^0$, being cited among others by the statements on prime-power torsion counts in characteristic zero and on good constant reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_finite_and_card_torsion_le_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.finite_and_card_torsion_le_of_natCast_ne_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) :
    Finite {c : Pic0 K F // n • c = 0} ∧
      Nat.card {c : Pic0 K F // n • c = 0} ≤ n ^ (2 * genusFF K F) := by sorry
