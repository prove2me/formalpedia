-- Prove2me | Theorems.Thm_DensInertW_mem_valPerp
-- name    : DensInertW.mem_valPerp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:53.130601+00:00
-- url     : https://prove2.me/theorems/bf4bbd51-3865-40e6-8c18-b7760c46c584
-- title:
--   Dens Inert W: mem val Perp
-- statement:
--   The Dens Inert W construction uses the mem val Perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L39-L47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
variable {L : Type} [Field L] {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem DensInertW.mem_valPerp {W : Submodule L (Fin n → L)} {e v : Fin n → L} :
    v ∈ valPerp q M W e ↔ v ∈ W ∧ hf q M v e = 0 := by sorry
