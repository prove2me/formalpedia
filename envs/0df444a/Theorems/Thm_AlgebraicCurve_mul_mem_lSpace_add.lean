-- Prove2me | Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_add
-- name    : AlgebraicCurve.mul_mem_lSpace_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/e45a86d1-b783-593a-b5ba-4b721ca55f41
-- title:
--   L(D)· L(E)⊆ L(D+E)
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $D,E$ be divisors of $F/K$, that is, finitely supported integer-valued functions on the type [`AlgebraicCurve.Place K F`](def/AlgebraicCurve_DivisorClassGroup.html#L22) of places of $F/K$ (a place being a valuation subring of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring). For a divisor $D$, the Riemann–Roch space `LSpace D` is the $K$-submodule of $F$ consisting of those $f$ with $v.\mathrm{adicValuation}(f) \le \exp(D\,v)$ for every place $v$, the inequality being one of multiplicatively written valuation values. The assertion is that if $f$ lies in `LSpace D` and $g$ lies in `LSpace E`, then the product $f g$ lies in `LSpace (D + E)`, where $D+E$ is the pointwise sum of the two finitely supported functions. Equivalently, in additive notation, $v(f)\ge -D(v)$ and $v(g)\ge -E(v)$ for all $v$ imply $v(fg)\ge -(D+E)(v)$.
--
--   This is the multiplicativity statement underlying the algebra structure on Riemann–Roch spaces of a function field: the spaces $L(D)$ form a filtered multiplicative system indexed by the divisor group. It is used in the dimension estimates leading to the genus bounds and the Riemann–Roch theory of the project, for instance in the construction of an $L$-polynomial over a finite base and in the surjectivity of residue maps for regular prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mul_mem_lSpace_add.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem mul_mem_lSpace_add {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {D E : Divisor K F} {f g : F}
    (hf : f ∈ LSpace D) (hg : g ∈ LSpace E) :
    f * g ∈ LSpace (D + E) := by sorry
