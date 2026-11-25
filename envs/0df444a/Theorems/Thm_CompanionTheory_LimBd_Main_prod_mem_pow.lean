-- Prove2me | Theorems.Thm_CompanionTheory_LimBd_Main_prod_mem_pow
-- name    : CompanionTheory.LimBd.Main.prod_mem_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:20.469642+00:00
-- url     : https://prove2.me/theorems/1309f973-c96b-4070-b32f-7abad79a615f
-- title:
--   Main: prod mem pow
-- statement:
--   The Main construction uses the prod mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/GeneratingFunctionPolynomial.lean#L25-L32

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

theorem CompanionTheory.LimBd.Main.prod_mem_pow {ι : Type} (s : Finset ι) (q : ι → B.Mat k r → ℂ) (h : ∀ i ∈ s, q i ∈ Letters k r) :
    ∏ i ∈ s, q i ∈ Letters k r ^ s.card := by sorry
