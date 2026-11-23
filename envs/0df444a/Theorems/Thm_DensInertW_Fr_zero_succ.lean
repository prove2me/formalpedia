-- Prove2me | Theorems.Thm_DensInertW_Fr_zero_succ
-- name    : DensInertW.Fr_zero_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:36.406665+00:00
-- url     : https://prove2.me/theorems/823099c3-0a2b-43eb-99b0-8fdfd8a1fbda
-- title:
--   Dens Inert W: Fr zero succ
-- statement:
--   The Dens Inert W construction uses the Fr zero succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensExactInertOf.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensExactInertOf.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf
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

theorem DensInertW.Fr_zero_succ (q d c : ℕ) :
    Fr q d 0 (c + 1) = (valZ q d - 1) * (q : ℤ) ^ (2 * c) * Fr q (d - 2) 0 c := by sorry
