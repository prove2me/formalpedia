-- Prove2me | Theorems.Thm_DensInertW_iso_li_cons
-- name    : DensInertW.iso_li_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:37.741004+00:00
-- url     : https://prove2.me/theorems/8a9f8286-f18e-4cd6-9dfe-979e5cfdc6b2
-- title:
--   Dens Inert W: iso li cons
-- statement:
--   The Dens Inert W construction uses the iso li cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/IsoPeel.lean#L29-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/IsoPeel.lean#L29-L51

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

theorem DensInertW.iso_li_cons {n c : ℕ} (x : Fin n → L) (U : Fin c → Fin n → L) (a : Fin c → L)
    (φ : (Fin n → L) →ₗ[L] L) (hφx : φ x = 1) (hφU : ∀ i, φ (U i) = 0)
    (hU : LinearIndependent L U) :
    LinearIndependent L (Fin.cons x (fun i => U i + a i • x) : Fin (c + 1) → Fin n → L) := by sorry
