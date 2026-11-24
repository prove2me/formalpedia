-- Prove2me | Theorems.Thm_CovecW_Hpk_mul_esI
-- name    : CovecW.Hpk_mul_esI
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:59:37.353953+00:00
-- url     : https://prove2.me/theorems/3b68e23a-0ef2-48df-9adc-0e077115eb99
-- title:
--   Covec W: Hpk mul es I
-- statement:
--   The Covec W construction uses the Hpk mul es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L94-L101

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

theorem CovecW.Hpk_mul_esI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : Fin r)
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (esI k r b) j = M (eI k r b) j := by sorry
