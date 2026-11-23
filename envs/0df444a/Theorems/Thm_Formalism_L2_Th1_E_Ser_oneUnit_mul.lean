-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_oneUnit_mul
-- name    : Formalism.L2.Th1.E.Ser.oneUnit_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:27.072454+00:00
-- url     : https://prove2.me/theorems/c83474af-d7fe-4a0e-92a7-1d3eee590b16
-- title:
--   Ser: one Unit mul
-- statement:
--   The Ser construction uses the one Unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L72-L73

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

theorem Formalism.L2.Th1.E.Ser.oneUnit_mul {f g : K⟦X⟧} (hf : OneUnit f) (hg : OneUnit g) : OneUnit (f * g) := by sorry
