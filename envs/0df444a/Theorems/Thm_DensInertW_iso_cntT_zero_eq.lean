-- Prove2me | Theorems.Thm_DensInertW_iso_cntT_zero_eq
-- name    : DensInertW.iso_cntT_zero_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:17.937827+00:00
-- url     : https://prove2.me/theorems/70f4d19a-5b6f-4ab3-b76c-d10a9b80b02b
-- title:
--   Dens Inert W: iso cnt T zero eq
-- statement:
--   The Dens Inert W construction uses the iso cnt T zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/IsoPeel.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/IsoPeel.lean#L58-L64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_IsoPeel
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
open DensInertW.Sub
variable {L : Type} [Field L]
open Classical

theorem DensInertW.iso_cntT_zero_eq [Fintype L] {n m q : ℕ} (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) :
    cntT q M W (0 : Matrix (Fin m) (Fin m) L) = (Finset.univ.filter (isoP (m := m) q M W)).card := by sorry
