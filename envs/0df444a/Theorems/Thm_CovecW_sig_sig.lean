-- Prove2me | Theorems.Thm_CovecW_sig_sig
-- name    : CovecW.sig_sig
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:06:29.852968+00:00
-- url     : https://prove2.me/theorems/005a4b9b-10ce-4f53-9f70-2753e546cc47
-- title:
--   Covec W: sig sig
-- statement:
--   The Covec W construction uses the sig sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianCovectors/HermBvecLeft.lean#L19-L23

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

theorem CovecW.sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by sorry
