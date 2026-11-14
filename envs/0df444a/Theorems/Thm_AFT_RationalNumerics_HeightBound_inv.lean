-- Prove2me | Theorems.Thm_AFT_RationalNumerics_HeightBound_inv
-- name    : AFT.RationalNumerics.HeightBound.inv
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:09:20.803543+00:00
-- url     : https://prove2.me/theorems/e1c4f728-7bf4-4b14-8a12-d1d241f289b3
-- title:
--   Rational inversion preserves binary height
-- statement:
--   Let $x\in\mathbb{Q}$ and $b\in\mathbb{N}$. If the absolute reduced numerator and denominator of $x$ are both at most $2^b$, then the same bounds hold for $x^{-1}$, with $0^{-1}=0$. This controls exact rational inversion in the constructive affine sampler.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/RationalHeight.lean, theorem HeightBound.inv. The original theorem type is preserved exactly.

import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Mathlib


/-! # Explicit binary height bounds for executable rational arithmetic -/
namespace AFT.RationalNumerics
end AFT.RationalNumerics
section AFT
section RationalNumerics
open AFT.RationalNumerics
open scoped BigOperators



namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
section HeightBound
open AFT.RationalNumerics.HeightBound

theorem AFT.RationalNumerics.HeightBound.inv {value : ℚ} {bits : ℕ} (h : HeightBound value bits) : HeightBound value⁻¹ bits := by sorry
