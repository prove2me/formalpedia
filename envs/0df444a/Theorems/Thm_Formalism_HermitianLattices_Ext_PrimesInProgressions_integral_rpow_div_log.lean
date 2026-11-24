-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_integral_rpow_div_log
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.integral_rpow_div_log
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:56.330656+00:00
-- url     : https://prove2.me/theorems/1c608405-f9b2-44a9-bc08-0d78f640a28f
-- title:
--   Primes In Progressions: integral rpow div log
-- statement:
--   The Primes In Progressions construction uses the integral rpow div log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L77-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L77-L107

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.integral_rpow_div_log {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    ∫ t in (2 : ℝ)..X, t ^ (β - 1) / Real.log t = liX (X ^ β) - liX ((2 : ℝ) ^ β) := by sorry
