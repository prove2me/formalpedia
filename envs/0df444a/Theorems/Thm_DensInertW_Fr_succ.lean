-- Prove2me | Theorems.Thm_DensInertW_Fr_succ
-- name    : DensInertW.Fr_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:33.668802+00:00
-- url     : https://prove2.me/theorems/269c257e-3259-42d5-bdd9-3e4930f3dbb0
-- title:
--   Dens Inert W: Fr succ
-- statement:
--   The Dens Inert W construction uses the Fr succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensExactInertOf.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/DensExactInertOf.lean#L14-L15

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

theorem DensInertW.Fr_succ (q d r c : ℕ) : Fr q d (r + 1) c = valN q d * Fr q (d - 1) r c := by sorry
