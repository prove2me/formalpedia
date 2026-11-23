-- Prove2me | Theorems.Thm_Formalism_UG_P_level_subgroup_local_standard
-- name    : Formalism.UG.P.level_subgroup_local_standard
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:34.551009+00:00
-- url     : https://prove2.me/theorems/5414035f-a730-41ee-9ab3-fbe8e3d7d96e
-- title:
--   P: level subgroup local standard
-- statement:
--   The P construction uses the level subgroup local standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L85-L88

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG

theorem Formalism.UG.P.level_subgroup_local_standard : Formalism.UG.LevelVLStd := by sorry
