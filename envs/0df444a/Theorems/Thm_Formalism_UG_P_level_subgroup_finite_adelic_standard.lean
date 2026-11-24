-- Prove2me | Theorems.Thm_Formalism_UG_P_level_subgroup_finite_adelic_standard
-- name    : Formalism.UG.P.level_subgroup_finite_adelic_standard
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:29.878782+00:00
-- url     : https://prove2.me/theorems/17e76034-8ab8-468c-9833-ea3291267466
-- title:
--   P: level subgroup finite adelic standard
-- statement:
--   The P construction uses the level subgroup finite adelic standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/LevelSubgroupFiniteAdelicStandard.lean#L80-L83

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

theorem Formalism.UG.P.level_subgroup_finite_adelic_standard : Formalism.UG.LevelAfLStd := by sorry
