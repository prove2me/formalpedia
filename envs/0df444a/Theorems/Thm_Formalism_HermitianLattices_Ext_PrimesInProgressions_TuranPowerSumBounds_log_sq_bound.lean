-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_log_sq_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.log_sq_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:34.41745+00:00
-- url     : https://prove2.me/theorems/aca08ecb-ce72-4a36-a374-859beb5215f7
-- title:
--   Turan Power Sum Bounds: log sq bound
-- statement:
--   The Turan Power Sum Bounds construction uses the log sq bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsPowerSumLowerBound.lean#L173-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsPowerSumLowerBound.lean#L173-L190

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.log_sq_bound (M : ℝ) (hM : 1 ≤ M) : Real.log (3 * M) ^ 2 ≤ 32 * Real.sqrt M := by sorry
