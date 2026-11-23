-- Prove2me | Theorems.Thm_Formalism_L2_SG_DensExact_densSplitDisplay_holds
-- name    : Formalism.L2.SG.DensExact.densSplitDisplay_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:53.913599+00:00
-- url     : https://prove2.me/theorems/179a91ca-f20f-42bf-b9a7-e2d99ef678e1
-- title:
--   Dens Exact: dens Split Display holds
-- statement:
--   The Dens Exact construction uses the dens Split Display holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/DensExact.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/DensExact.lean#L87-L105

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.DensExact

theorem Formalism.L2.SG.DensExact.densSplitDisplay_holds : DensSplitDisplay := by sorry
