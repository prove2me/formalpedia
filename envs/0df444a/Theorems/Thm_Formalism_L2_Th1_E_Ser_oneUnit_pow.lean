-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_oneUnit_pow
-- name    : Formalism.L2.Th1.E.Ser.oneUnit_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:25.224721+00:00
-- url     : https://prove2.me/theorems/f0ce6515-1832-426f-be42-bb9a791a594c
-- title:
--   Ser: one Unit pow
-- statement:
--   The Ser construction uses the one Unit pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L75-L76

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

theorem Formalism.L2.Th1.E.Ser.oneUnit_pow {f : K⟦X⟧} (hf : OneUnit f) (n : ℕ) : OneUnit (f ^ n) := by sorry
