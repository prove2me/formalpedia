-- Prove2me | Theorems.Thm_CovecW_herm_bvec_left
-- name    : CovecW.herm_bvec_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:00:11.715598+00:00
-- url     : https://prove2.me/theorems/199dc2c7-c5c1-4569-83a2-6dea976442f4
-- title:
--   Covec W: herm bvec left
-- statement:
--   The Covec W construction uses the herm bvec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L122-L130

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

theorem CovecW.herm_bvec_left (k r : ℕ) (H M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x y : Fin (2 * r + k + 1)) :
    herm H (M *ᵥ bvec y) (bvec x) = (H * M) x y := by sorry
