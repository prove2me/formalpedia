-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedExists0Pf_reduction_exists
-- name    : Formalism.L2.SG.Pf.RedExists0Pf.reduction_exists
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:30:07.285187+00:00
-- url     : https://prove2.me/theorems/be722f2a-1d7f-4573-912f-ca167d4641b6
-- title:
--   Red Exists0 Pf: reduction exists
-- statement:
--   The Red Exists0 Pf construction uses the reduction exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionExists.lean#L14-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionExists.lean#L14-L83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedExists0Pf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf

theorem Formalism.L2.SG.Pf.RedExists0Pf.reduction_exists : Formalism.L2.SG.Pf.RowDictPf.RedExists0 := by sorry
