-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_tInZ_of
-- name    : Formalism.L2.Th1.A.tInZ_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:51.86506+00:00
-- url     : https://prove2.me/theorems/78c4a3df-fd0a-49eb-8d29-3116e98ff7f7
-- title:
--   A: t In Z of
-- statement:
--   The A construction uses the t In Z of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L340-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/TwoTorsionIntegral.lean#L340-L349

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Two

theorem Formalism.L2.Th1.A.tInZ_of (hS : WpShape.{u}) : TInZ.{u} := by sorry
