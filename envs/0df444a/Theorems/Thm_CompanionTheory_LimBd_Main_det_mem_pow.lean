-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_det_mem_pow
-- name    : CompanionTheory.LimBd.Main.det_mem_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:23.626682+00:00
-- url     : https://prove2.me/theorems/a04c6467-df0a-527b-93e1-58f495155a6a
-- title:
--   Main: det mem pow
-- statement:
--   The Main construction uses the det mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L34-L42

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

theorem CompanionTheory.LimBd.Main.det_mem_pow {m : ℕ} (Z : B.Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ a b, (fun g => Z g a b) ∈ Letters k r) : (fun g => (Z g).det) ∈ Letters k r ^ m := by sorry
