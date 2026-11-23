-- Prove2me | Theorems.Thm_DensInertW_finrank_valPerp
-- name    : DensInertW.finrank_valPerp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:39:05.553807+00:00
-- url     : https://prove2.me/theorems/be8828e9-1e7d-46b9-808a-67287e3e5014
-- title:
--   Dens Inert W: finrank val Perp
-- statement:
--   The Dens Inert W construction uses the finrank val Perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L49-L60

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

theorem DensInertW.finrank_valPerp {W : Submodule L (Fin n → L)} {e : Fin n → L} (he : e ∈ W)
    (hb : hf q M e e ≠ 0) : finrank L (valPerp q M W e) + 1 = finrank L W := by sorry
