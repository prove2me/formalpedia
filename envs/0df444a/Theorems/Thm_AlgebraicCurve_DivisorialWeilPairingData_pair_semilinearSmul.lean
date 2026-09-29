-- Prove2me | Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
-- name    : AlgebraicCurve.DivisorialWeilPairingData.pair_semilinearSmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/057adf86-1728-5064-8da1-5eed753a0735
-- title:
--   Semilinear equivariance of the divisorial Weil pairing
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $n$ be a nonzero natural number, and assume `HasPrincipalDivisors K F`, i.e. every nonzero $f \in F$ admits a divisor $D$ on the places of $F/K$ with $D(v) = \mathrm{ord}_v(f)$ for all $v$ and $\deg D = 0$. Let $e$ be a divisorial Weil pairing datum of level $n$: a function $\mathrm{pair}$ on pairs of $n$-torsion classes of $\mathrm{Pic}^0(F/K)$ (degree-zero divisors modulo principal ones, torsion taken for multiplication by $n$ over $\mathbb{Z}$) with values in $K$, which on the classes $\mathrm{classLeft}$, $\mathrm{classRight}$ attached to any Weil datum of level $n$ returns that datum's pairing value, and which satisfies the moving property: every $n$-torsion class is represented by a degree-zero divisor supported on rational places avoiding any prescribed finite set of places. Let $g$ be an element of `SemilinearAut K F`, that is a pair consisting of a ring automorphism of $F$ and a ring automorphism of $K$ which are compatible with the structure map $K \to F$, the second component being $\mathrm{baseAut}\,g$; $g$ acts on places, divisors, and hence on $n$-torsion classes. Then for all $n$-torsion classes $x, y$ one has $e.\mathrm{pair}(g \cdot x, g \cdot y) = (\mathrm{baseAut}\,g)\bigl(e.\mathrm{pair}(x,y)\bigr)$.
--
--   This is the Galois (more precisely semilinear) equivariance of the Weil pairing on the $n$-torsion of the Jacobian, in the divisorial formulation used in this development. It is what converts the pairing into information about the Galois action on Tate modules of Jacobians, and it is cited for the determination of the semilinear action on the Tate module as well as in the computations of pairing values on the modular curves $X_1$ and their Néron models at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.DivisorialWeilPairingData.pair_semilinearSmul {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n]
    [HasPrincipalDivisors K F]
    (e : DivisorialWeilPairingData K F n) (g : SemilinearAut K F)
    (x y : Pic0.torsion K F n) :
    e.pair (g • x) (g • y) = SemilinearAut.baseAut g (e.pair x y) := by sorry
