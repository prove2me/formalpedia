-- Prove2me | Theorems.Thm_DensInertW_Sub_q_ne_zero_of_inv
-- name    : DensInertW.Sub.q_ne_zero_of_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:47.674307+00:00
-- url     : https://prove2.me/theorems/1105d09c-bb93-43a3-8596-b195d9b1c650
-- title:
--   Sub: q ne zero of inv
-- statement:
--   The Sub construction uses the q ne zero of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L9-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]

theorem DensInertW.Sub.q_ne_zero_of_inv {q : ℕ} (hinv : ∀ a : L, (a ^ q) ^ q = a) : q ≠ 0 := by sorry
