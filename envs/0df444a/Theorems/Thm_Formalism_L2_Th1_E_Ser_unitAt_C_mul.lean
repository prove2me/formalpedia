-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_C_mul
-- name    : Formalism.L2.Th1.E.Ser.unitAt_C_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:51.237804+00:00
-- url     : https://prove2.me/theorems/9e86fca6-f91e-4062-98f7-bd25787dc8cf
-- title:
--   Ser: unit At C mul
-- statement:
--   The Ser construction uses the unit At C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L162-L167

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

theorem Formalism.L2.Th1.E.Ser.unitAt_C_mul {k : ℕ} {f : K⟦X⟧} {a : K} (ha : ‖a‖ = 1) (hf : UnitAt k f) :
    UnitAt k (C a * f) := by sorry
