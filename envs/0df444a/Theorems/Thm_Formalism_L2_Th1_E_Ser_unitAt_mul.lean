-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_mul
-- name    : Formalism.L2.Th1.E.Ser.unitAt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:36.892555+00:00
-- url     : https://prove2.me/theorems/38b8e5a7-bd23-4a9f-afbf-3e34cea6c7ca
-- title:
--   Ser: unit At mul
-- statement:
--   The Ser construction uses the unit At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L112-L118

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.L2.Th1.E.Ser.unitAt_mul {j k : ℕ} {f g : K⟦X⟧} (hf : UnitAt j f) (hg : UnitAt k g) :
    UnitAt (j + k) (f * g) := by sorry
