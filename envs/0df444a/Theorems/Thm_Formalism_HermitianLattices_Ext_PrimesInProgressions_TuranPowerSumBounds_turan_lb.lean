-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_turan_lb
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.turan_lb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:18.596816+00:00
-- url     : https://prove2.me/theorems/822eb758-cdd8-4b70-a450-e12b7f9771dd
-- title:
--   Turan Power Sum Bounds: turan lb
-- statement:
--   The Turan Power Sum Bounds construction uses the turan lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsPowerSumLowerBound.lean#L109-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsPowerSumLowerBound.lean#L109-L138

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.turan_lb (C : ℝ) (hC : 0 < C) (a n m : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1)) ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) := by sorry
