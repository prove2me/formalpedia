-- Prove2me | Theorems.Thm_DensInertW_cg_map_mul
-- name    : DensInertW.cg_map_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:39:09.77719+00:00
-- url     : https://prove2.me/theorems/d47275f4-45f1-469d-ab7b-089b2a8069eb
-- title:
--   Dens Inert W: cg map mul
-- statement:
--   The Dens Inert W construction uses the cg map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L106-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L106-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW

theorem DensInertW.cg_map_mul (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m : ℕ}
    (A C : Matrix (Fin m) (Fin m) L) :
    (A * C).map (fun y => y ^ Fintype.card K) =
      A.map (fun y => y ^ Fintype.card K) * C.map (fun y => y ^ Fintype.card K) := by sorry
