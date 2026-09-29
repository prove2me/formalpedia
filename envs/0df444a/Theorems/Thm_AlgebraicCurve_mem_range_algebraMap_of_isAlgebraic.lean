-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic
-- name    : AlgebraicCurve.mem_range_algebraMap_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/f49c3b95-9f3f-5ad6-8ab7-dd0f69612bee
-- title:
--   Algebraic elements over an algebraically closed base are constants
-- statement:
--   Let $K$ and $L$ be fields, with $L$ a $K$-algebra, and suppose $K$ is algebraically closed. Let $x$ be an element of $L$ which is algebraic over $K$, that is, $x$ is a root of some nonzero polynomial with coefficients in $K$. The conclusion is that $x$ lies in the range of the structure map $\mathrm{algebraMap} : K \to L$, i.e. $x$ is of the form $a \cdot 1$ for some $a \in K$. No separability, finiteness or normality hypothesis is imposed on the extension, and the algebra map is not assumed injective beyond what follows from $K$ being a field and $L$ nonzero.
--
--   This is the standard fact that an algebraically closed field admits no proper algebraic extension, in the relative form: the algebraic closure of $K$ inside any $K$-algebra field $L$ is $K$ itself. Within the project it is used when comparing regular differentials on a curve with those of a constant field extension, in [`AlgebraicCurve.exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension`](thm.html#AlgebraicCurve.exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension), to recognise elements algebraic over the constant field as constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic.lean

import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.mem_range_algebraMap_of_isAlgebraic {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] {x : L} (hx : IsAlgebraic K x) :
    x ∈ (algebraMap K L).range := by sorry
