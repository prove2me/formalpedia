-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_herm_letter
-- name    : CompanionTheory.LimBd.Main.herm_letter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:41.114384+00:00
-- url     : https://prove2.me/theorems/05daf539-efcf-5feb-bc4d-8bdd335c9b14
-- title:
--   Main: herm letter
-- statement:
--   The Main construction uses the herm letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L49-L53

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

theorem CompanionTheory.LimBd.Main.herm_letter (x y : Fin (2 * r + k + 1) → ℂ) :
    (fun g : B.Mat k r => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ x) y) ∈ Letters k r := by sorry
