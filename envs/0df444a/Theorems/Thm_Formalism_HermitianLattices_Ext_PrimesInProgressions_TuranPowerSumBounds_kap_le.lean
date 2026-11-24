-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_kap_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.kap_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:32.249054+00:00
-- url     : https://prove2.me/theorems/751dff5f-24aa-4088-a49b-5ba0d3ffdf1d
-- title:
--   Turan Power Sum Bounds: kap le
-- statement:
--   The Turan Power Sum Bounds construction uses the kap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TwentyFiveMulSmallConstant.lean#L98-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TwentyFiveMulSmallConstant.lean#L98-L113

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.kap_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : kap a D ≤ th a := by sorry
