-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_logMulAbsAddTwoLeTwoMulLog
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.logMulAbsAddTwoLeTwoMulLog
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:46.280055+00:00
-- url     : https://prove2.me/theorems/7562bd43-d55d-4c49-9a4f-3b8e3344c50e
-- title:
--   Primes In Progressions: log Mul Abs Add Two Le Two Mul Log
-- statement:
--   The Primes In Progressions construction uses the log Mul Abs Add Two Le Two Mul Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L17-L28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.logMulAbsAddTwoLeTwoMulLog (M : ℕ) (T t : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (ht : |t| ≤ T) :
    Real.log ((M : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by sorry
