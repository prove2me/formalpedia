-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_AddSigma_of
-- name    : Formalism.L2.Th1.B.AddSigma_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:21.643351+00:00
-- url     : https://prove2.me/theorems/b889fd1b-525b-4292-b757-ec882d5d073a
-- title:
--   B: Add Sigma of
-- statement:
--   The B construction uses the Add Sigma of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L425-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/PderivZeroZeroWeierstrassDifference.lean#L425-L476

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Add0

theorem Formalism.L2.Th1.B.AddSigma_of (hL : AddSigmaLog) (h1 : ExpLogRules) (h3 : ExpLogSubst) (h9 : DqRule) :
    AddSigma := by sorry
