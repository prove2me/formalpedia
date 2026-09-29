-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
-- name    : AlgebraicCurve.RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/5d4c35f9-694f-5610-aa74-d68bc8fe05e0
-- title:
--   Finite-dimensionality of L(0) when the constants are K
-- statement:
--   Let $K$ be a field and $F$ a field equipped with a $K$-algebra structure. A place of $K$ in $F$ is a valuation subring of $F$ that contains $\operatorname{image}(K \to F)$, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, and for a divisor $D$ the space $\mathrm{LSpace}\,D = \mathrm{riemannRochSpace}\,D$ is the $K$-submodule of those $f \in F$ with $v(f) \le \exp(D\,v)$ for every place $v$, where $v$ denotes the associated valuation. For $D = 0$ this is the set of $f$ lying in every place's valuation ring. The hypothesis `ConstantsAreBase K F` asserts precisely that this space $\mathrm{LSpace}\,(0)$ coincides with the range of the $K$-linear map $K \to F$. Under this hypothesis the conclusion is that $\mathrm{LSpace}\,(0)$ is a finite-dimensional $K$-vector space (its dimension being $1$, although only finiteness is asserted).
--
--   This is the statement that a function field whose field of constants is the base field has finite-dimensional (indeed one-dimensional) Riemann–Roch space attached to the zero divisor. It serves to discharge the `FiniteDimensional K (LSpace 0)` side condition appearing in the divisor and constant-field-extension results built on Riemann–Roch, such as the bounds on $\dim_K L(D)$ under place reduction and the torsion descent statements for constant field extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase (K : Type*) [Field K] (F : Type*) [Field F] [Algebra K F] (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by sorry
