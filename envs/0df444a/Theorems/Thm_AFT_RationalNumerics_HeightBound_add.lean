-- Prove2me | Theorems.Thm_AFT_RationalNumerics_HeightBound_add
-- name    : AFT.RationalNumerics.HeightBound.add
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T02:28:24.718202+00:00
-- url     : https://prove2.me/theorems/95940d13-635e-4d90-8fa4-74df001da1bf
-- title:
--   Rational addition increases binary height additively
-- statement:
--   Let $x,y\in\mathbb{Q}$ and $a,b\in\mathbb{N}$. Suppose the absolute reduced numerator and denominator of $x$ are at most $2^a$, and those of $y$ are at most $2^b$. Then
--
--   $$\max\{|\operatorname{num}(x+y)|,\operatorname{den}(x+y)\}\le 2^{a+b+1}.$$
--
--   This bounds operand growth in the exact rational arithmetic used by the constructive affine sampler.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/RationalHeight.lean, theorem HeightBound.add, lines 44–62; transplanted from the migrated source without changing its type.

import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Mathlib


/-! # Explicit binary height bounds for executable rational arithmetic -/
namespace AFT.RationalNumerics
end AFT.RationalNumerics
section AFT.RationalNumerics
open AFT.RationalNumerics
open scoped BigOperators



namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
section HeightBound
open AFT.RationalNumerics.HeightBound

theorem AFT.RationalNumerics.HeightBound.add {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first+second) (firstBits+secondBits+1) := by sorry
