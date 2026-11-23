-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_nonneg
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.liX_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:29.812145+00:00
-- url     : https://prove2.me/theorems/d667f135-e2c1-488d-9e89-a4bed264a375
-- title:
--   Logarithmic Integral Bounds: li X nonneg
-- statement:
--   The Logarithmic Integral Bounds construction uses the li X nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L70-L73

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.liX_nonneg {a : ℝ} (ha : 2 ≤ a) : 0 ≤ liX a := by sorry
