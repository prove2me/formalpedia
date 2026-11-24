-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_liX_two_rpow_abs
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.liX_two_rpow_abs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:05.733025+00:00
-- url     : https://prove2.me/theorems/dad7e99d-7010-4a9f-b9b9-107ddb6766a4
-- title:
--   Primes In Progressions: li X two rpow abs
-- statement:
--   The Primes In Progressions construction uses the li X two rpow abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L188-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L188-L210

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.liX_two_rpow_abs {β : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) : |liX ((2 : ℝ) ^ β)| ≤ 4 := by sorry
