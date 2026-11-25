-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_dmin_mem
-- name    : CompanionTheory.LimBd.Main.dmin_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:55.558264+00:00
-- url     : https://prove2.me/theorems/c74150fb-d735-4926-b5e0-f803250c7456
-- title:
--   Main: dmin mem
-- statement:
--   The Main construction uses the dmin mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L67-L81

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

theorem CompanionTheory.LimBd.Main.dmin_mem (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    (fun g : B.Mat k r => ((Complex.normSq (Formalism.QuantumDeterminants.Dmin k r z z' g l) : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2) := by sorry
