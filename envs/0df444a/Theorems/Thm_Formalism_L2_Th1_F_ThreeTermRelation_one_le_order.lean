-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_one_le_order
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.one_le_order
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:06.683557+00:00
-- url     : https://prove2.me/theorems/701d4d14-5563-48c4-83f6-911172553814
-- title:
--   Three Term Relation: one le order
-- statement:
--   The Three Term Relation construction uses the one le order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L195-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L195-L201

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThreeTermRelation
variable (L : PeriodPair) (b c : ℂ)

theorem Formalism.L2.Th1.F.ThreeTermRelation.one_le_order {f : ℂ → ℂ} {z : ℂ} (han : AnalyticAt ℂ f z) (h0 : f z = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z := by sorry
