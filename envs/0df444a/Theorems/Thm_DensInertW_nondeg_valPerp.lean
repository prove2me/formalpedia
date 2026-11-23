-- Prove2me | Theorems.Thm_DensInertW_nondeg_valPerp
-- name    : DensInertW.nondeg_valPerp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:14.610617+00:00
-- url     : https://prove2.me/theorems/c195b149-8ea3-41e0-bc9d-8207710f3a1b
-- title:
--   Dens Inert W: nondeg val Perp
-- statement:
--   The Dens Inert W construction uses the nondeg val Perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L115-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankValPerp.lean#L115-L132

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

theorem DensInertW.nondeg_valPerp [Fintype L] (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M)
    {W : Submodule L (Fin n → L)} (hW : NonDeg (Fintype.card K) M W) {e : Fin n → L}
    (he : e ∈ W) (hb : hf (Fintype.card K) M e e ≠ 0) :
    NonDeg (Fintype.card K) M (valPerp (Fintype.card K) M W e) := by sorry
