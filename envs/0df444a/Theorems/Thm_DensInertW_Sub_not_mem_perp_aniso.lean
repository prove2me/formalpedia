-- Prove2me | Theorems.Thm_DensInertW_Sub_not_mem_perp_aniso
-- name    : DensInertW.Sub.not_mem_perp_aniso
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:17:50.458102+00:00
-- url     : https://prove2.me/theorems/0679359f-1661-4fde-ae61-cfefeec56828
-- title:
--   Sub: not mem perp aniso
-- statement:
--   The Sub construction uses the not mem perp aniso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L146-L148

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

theorem DensInertW.Sub.not_mem_perp_aniso (W : Submodule L (Fin n → L)) (e : Fin n → L)
    (hee : hf q M e e ≠ 0) : e ∉ W ⊓ LinearMap.ker (hfL q M e) := by sorry
