-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_phase_zero_alt
-- name    : CompanionTheory.LimBd.Main.phase_zero_alt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:03.509656+00:00
-- url     : https://prove2.me/theorems/ce6b0d1a-8f96-479b-8590-b99b2864a958
-- title:
--   Main: phase zero alt
-- statement:
--   The Main construction uses the phase zero alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/BetaAtInfinityZero.lean#L48-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/BetaAtInfinityZero.lean#L48-L75

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_BetaAtInfinityZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk MeasureTheory
open scoped InnerProductSpace

theorem CompanionTheory.LimBd.Main.phase_zero_alt : PhZero := by sorry
