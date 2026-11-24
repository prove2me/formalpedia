-- Prove2me | Theorems.Thm_CovecW_Hpk_mul_eI
-- name    : CovecW.Hpk_mul_eI
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:02:14.831324+00:00
-- url     : https://prove2.me/theorems/6eb28af4-b5af-465e-8c87-6360ec14de56
-- title:
--   Covec W: Hpk mul e I
-- statement:
--   The Covec W construction uses the Hpk mul e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L85-L92

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

theorem CovecW.Hpk_mul_eI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (eI k r a) j = M (esI k r a) j := by sorry
