-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_iff_integral
-- name    : Formalism.L2.Th1.E.Ser.intS_iff_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:22.634616+00:00
-- url     : https://prove2.me/theorems/6d29d0fd-475f-4993-ae31-773aad3d83ec
-- title:
--   Ser: int S iff integral
-- statement:
--   The Ser construction uses the int S iff integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L104-L110

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

theorem Formalism.L2.Th1.E.Ser.intS_iff_integral (f : K⟦X⟧) : IntS f ↔ Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f := by sorry
