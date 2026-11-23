-- Prove2me | Theorems.Thm_DensInertW_val_fibre
-- name    : DensInertW.val_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:54.63263+00:00
-- url     : https://prove2.me/theorems/11bc0c71-2316-41a9-8d77-8bc54fc54054
-- title:
--   Dens Inert W: val fibre
-- statement:
--   The Dens Inert W construction uses the val fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L134-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L134-L144

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}

theorem DensInertW.val_fibre [Fintype L] [DecidableEq L] (h2 : finrank K L = 2) (b t : L) (hb : b ≠ 0)
    (hbq : b ^ Fintype.card K = b) (ht : t ^ Fintype.card K = t) :
    #{l : L | l ^ (Fintype.card K + 1) * b = t} = if t = 0 then 1 else Fintype.card K + 1 := by sorry
