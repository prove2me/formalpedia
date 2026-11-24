-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_pow
-- name    : Formalism.L2.Th1.E.Ser.unitAt_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:43.199083+00:00
-- url     : https://prove2.me/theorems/383a1587-06bb-43f3-ba7e-8a89e6914747
-- title:
--   Ser: unit At pow
-- statement:
--   The Ser construction uses the unit At pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L120-L123

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

theorem Formalism.L2.Th1.E.Ser.unitAt_pow {k : ℕ} {f : K⟦X⟧} (hf : UnitAt k f) (n : ℕ) : UnitAt (k * n) (f ^ n) := by sorry
