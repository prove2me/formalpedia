-- Prove2me | Theorems.Thm_CovecW_sgn_sig
-- name    : CovecW.sgn_sig
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:00:28.132963+00:00
-- url     : https://prove2.me/theorems/010812d7-a6b2-44cb-8184-ef4991c29dff
-- title:
--   Covec W: sgn sig
-- statement:
--   The Covec W construction uses the sgn sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L27-L31

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

theorem CovecW.sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by sorry
