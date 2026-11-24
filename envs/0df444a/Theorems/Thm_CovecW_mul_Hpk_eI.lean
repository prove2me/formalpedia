-- Prove2me | Theorems.Thm_CovecW_mul_Hpk_eI
-- name    : CovecW.mul_Hpk_eI
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:00:05.419085+00:00
-- url     : https://prove2.me/theorems/4ed606c7-71ff-46f3-b9fd-65df6c6ee021
-- title:
--   Covec W: mul Hpk e I
-- statement:
--   The Covec W construction uses the mul Hpk e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L103-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L103-L115

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

theorem CovecW.mul_Hpk_eI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (i : Fin (2 * r + k + 1)) : (M * Hpk k r) i (eI k r a) = M i (esI k r a) := by sorry
