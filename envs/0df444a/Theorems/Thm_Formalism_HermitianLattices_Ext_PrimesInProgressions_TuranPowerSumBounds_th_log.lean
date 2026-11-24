-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_th_log
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.th_log
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:51.851044+00:00
-- url     : https://prove2.me/theorems/3128e078-4406-4b94-8452-bc6343094a6c
-- title:
--   Turan Power Sum Bounds: th log
-- statement:
--   The Turan Power Sum Bounds construction uses the th log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TwentyFiveMulSmallConstant.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TwentyFiveMulSmallConstant.lean#L33-L38

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.th_log (a : ℕ) : 2 * th a * Real.log (rr a) = 1 := by sorry
