-- Prove2me | Theorems.Thm_DensInertW_Sub_hf_add_right
-- name    : DensInertW.Sub.hf_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:21.916383+00:00
-- url     : https://prove2.me/theorems/50572c0b-13b2-4c59-82e2-e5c79dc1eeb5
-- title:
--   Sub: hf add right
-- statement:
--   The Sub construction uses the hf add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L49-L51

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

theorem DensInertW.Sub.hf_add_right (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (x y y' : Fin n → L) :
    hf q M x (y + y') = hf q M x y + hf q M x y' := by sorry
