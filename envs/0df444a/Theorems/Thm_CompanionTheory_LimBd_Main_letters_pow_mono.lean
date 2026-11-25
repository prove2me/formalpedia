-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_letters_pow_mono
-- name    : CompanionTheory.LimBd.Main.letters_pow_mono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:35.423602+00:00
-- url     : https://prove2.me/theorems/1afbc3de-7e11-52d3-aa48-c6662f743169
-- title:
--   Main: letters pow mono
-- statement:
--   The Main construction uses the letters pow mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L19-L23

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

theorem CompanionTheory.LimBd.Main.letters_pow_mono {d e : ℕ} (hde : d ≤ e) {q : B.Mat k r → ℂ} (h : q ∈ Letters k r ^ d) :
    q ∈ Letters k r ^ e := by sorry
