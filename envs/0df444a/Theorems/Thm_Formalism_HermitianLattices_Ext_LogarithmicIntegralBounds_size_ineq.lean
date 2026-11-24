-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_size_ineq
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.size_ineq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:26.598458+00:00
-- url     : https://prove2.me/theorems/ce565ff6-851e-426d-b589-e51bab930ec2
-- title:
--   Logarithmic Integral Bounds: size ineq
-- statement:
--   The Logarithmic Integral Bounds construction uses the size ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L175-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L175-L203

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.size_ineq {c Y Λ : ℝ} (hc0 : 0 < c) (hY0 : 0 < Y) (h80 : 80 * Λ ≤ Y)
    (hlog : Real.log (320 / c) ≤ Y / 20) :
    4 * Real.exp (Y * (9 / 10)) ≤ c * Real.exp Y / (2 * Y * Real.exp Λ ^ 2) := by sorry
