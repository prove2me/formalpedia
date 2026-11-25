-- Prove2me | Theorems.Thm_DensInertW_Sub_hf_zero_right
-- name    : DensInertW.Sub.hf_zero_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:05.052892+00:00
-- url     : https://prove2.me/theorems/7fbdb7c4-4a53-462f-9714-01189dffc44d
-- title:
--   Sub: hf zero right
-- statement:
--   The Sub construction uses the hf zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L68-L69

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
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem DensInertW.Sub.hf_zero_right (hq : q ≠ 0) (x : Fin n → L) : hf q M x 0 = 0 := by sorry
