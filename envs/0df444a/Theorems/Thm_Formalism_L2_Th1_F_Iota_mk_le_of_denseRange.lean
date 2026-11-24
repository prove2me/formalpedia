-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Iota_mk_le_of_denseRange
-- name    : Formalism.L2.Th1.F.Iota.mk_le_of_denseRange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:15:59.735432+00:00
-- url     : https://prove2.me/theorems/30dcf251-9647-4a68-a3df-7ac0b3ab6cde
-- title:
--   Iota: mk le of dense Range
-- statement:
--   The Iota construction uses the mk le of dense Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MkLeOfDenseRange.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MkLeOfDenseRange.lean#L9-L23

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Cardinal Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Iota

theorem Formalism.L2.Th1.F.Iota.mk_le_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by sorry
