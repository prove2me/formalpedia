-- Prove2me | Theorems.Thm_AlgebraicCurve_constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
-- name    : AlgebraicCurve.constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/c641e2e8-d7ad-5818-8462-a94c3d598ade
-- title:
--   Degree invariance of the constant-field pullback of divisors
-- statement:
--   Let $K$, $K'$, $F$, $F'$ be fields with $K'$ a $K$-algebra, $F$ a $K$-algebra, $F'$ an algebra over both $K'$ and $F$, the scalar towers $K \to K' \to F'$ and $K \to F \to F'$ being compatible with the given $K$-algebra structure on $F'$. Assume $K$ perfect, $K'/K$ algebraic, $F'/F$ integral, $F$ essentially of finite type over $K$, and that both $F/K$ and $F'/K'$ are curves in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): principal divisors exist (every $f \neq 0$ admits a finitely supported divisor whose value at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$), every place has residue field finite-dimensional over the base field, and the module of Kähler differentials is free of rank one over the function field. Assume further that $F'$ is generated as an $F$-algebra by the image of $K'$, and that every element of $F$ algebraic over $K$ lies in the image of $K$. Then the constant-field degree formula holds: for every divisor $D$ of $F/K$ (a finitely supported $\mathbb{Z}$-valued function on the places of $F/K$, places being proper valuation subrings of $F$ containing the image of $K$ and which are principal ideal rings), the degree of the constant-field pullback `Divisor.pullbackConstants K' F' D`, a divisor of $F'/K'$, equals the degree of $D$, degrees being the sums $\sum_v D(v)\,\deg v$.
--
--   This is the degree-preservation part of the classical theory of constant field extensions of function fields (Stichtenoth, Theorem III.6.3): the constant extension $F' = F\cdot K'$ induces a degree-preserving map on divisor groups. It feeds the comparison of genera and of degree-zero divisor class groups under constant extension, and the analysis of Frobenius fixed points on $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [PerfectField K] [Algebra.IsAlgebraic K K'] [Algebra.IsIntegral F F']
    [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) :
    AlgebraicCurve.ConstantFieldDegreeFormula K K' F F' := by sorry
