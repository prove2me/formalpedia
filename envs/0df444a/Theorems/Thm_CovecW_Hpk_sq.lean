-- Prove2me | Theorems.Thm_CovecW_Hpk_sq
-- name    : CovecW.Hpk_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:00:01.893043+00:00
-- url     : https://prove2.me/theorems/048996b9-3321-46fc-bca1-b6a819a49ff0
-- title:
--   Covec W: Hpk sq
-- statement:
--   The Covec W construction uses the Hpk sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L40-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L40-L55

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CovecW
open Formalism.QuantumDeterminants

theorem CovecW.Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by sorry
