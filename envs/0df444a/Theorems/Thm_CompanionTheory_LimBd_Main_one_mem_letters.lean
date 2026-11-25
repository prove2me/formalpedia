-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_one_mem_letters
-- name    : CompanionTheory.LimBd.Main.one_mem_letters
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:59.542062+00:00
-- url     : https://prove2.me/theorems/91a5c3fc-15ee-47f5-85bb-6efe25ecdef9
-- title:
--   Main: one mem letters
-- statement:
--   The Main construction uses the one mem letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L13-L13

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
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
open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped ComplexConjugate
variable {k r : ℕ}

theorem CompanionTheory.LimBd.Main.one_mem_letters : (1 : B.Mat k r → ℂ) ∈ Letters k r := by sorry
