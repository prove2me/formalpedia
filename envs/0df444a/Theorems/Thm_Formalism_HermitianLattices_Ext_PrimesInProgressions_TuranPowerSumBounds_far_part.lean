-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_far_part
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.far_part
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:57.036992+00:00
-- url     : https://prove2.me/theorems/71506dc4-beda-47fd-8c9b-e3596621726d
-- title:
--   Turan Power Sum Bounds: far part
-- statement:
--   The Turan Power Sum Bounds construction uses the far part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/UbTerms.lean#L52-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/UbTerms.lean#L52-L66

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_UbTerms
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.far_part (a : ℕ) (S : ℝ) (j : ℕ) (hj2 : 2 ≤ j) (hS : S ≤ 1 + j) :
    eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by sorry
