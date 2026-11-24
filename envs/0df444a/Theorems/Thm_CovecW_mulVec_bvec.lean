-- Prove2me | Theorems.Thm_CovecW_mulVec_bvec
-- name    : CovecW.mulVec_bvec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:07:41.814368+00:00
-- url     : https://prove2.me/theorems/f14ad88c-38d4-4780-b458-06eec1489dcf
-- title:
--   Covec W: mul Vec bvec
-- statement:
--   The Covec W construction uses the mul Vec bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L117-L120

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

theorem CovecW.mulVec_bvec (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (y : Fin (2 * r + k + 1)) :
    M *ᵥ bvec y = fun i => M i y := by sorry
