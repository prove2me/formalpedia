-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem
-- name    : AlgebraicCurve.Place.exists_not_mem_and_forall_ne_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/595f4dfe-7984-5c18-a1b8-5af20b8d7d17
-- title:
--   A function with a pole at exactly one place
-- statement:
--   Let $K$ be a perfect field and $F$ a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ and $\deg D = 0$; for every place $v$ the residue field of $v$ is a finite $K$-module; and the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Assume further `ConstantsAreBase K F`, i.e. the Riemann–Roch space $L(0)$ of the zero divisor coincides with the image of $K$ in $F$ under the structure map. Then for every place $v$ of $F/K$ there exists $f \in F$ which does not lie in the valuation subring of $v$ but lies in the valuation subring of every place $w \neq v$; that is, $f$ has a pole at $v$ and no pole elsewhere.
--
--   This is the classical corollary of Riemann's inequality asserting that each place of a one-variable function field with full constant field $K$ carries a function whose only pole is at that place. It is used in this development to produce transcendental elements with prescribed polar behaviour, feeding [`AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne`](thm.html#AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_not_mem_and_forall_ne_mem
    {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F) (v : AlgebraicCurve.Place K F) :
    ∃ f : F, f ∉ v.toValuationSubring ∧
      ∀ w : AlgebraicCurve.Place K F, w ≠ v → f ∈ w.toValuationSubring := by sorry
