-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Main_norm_natCast_of_dvd
-- name    : Formalism.L2.Th1.E.Main.norm_natCast_of_dvd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:55.804602+00:00
-- url     : https://prove2.me/theorems/8dfd88e4-b7ab-4bff-810a-5cd145b1d65e
-- title:
--   Main: norm nat Cast of dvd
-- statement:
--   The Main construction uses the norm nat Cast of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L28-L37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Main
variable {K : Type} [NormedField K]

theorem Formalism.L2.Th1.E.Main.norm_natCast_of_dvd [IsUltrametricDist K] {n N : ℕ} (h : n ∣ N) (hN : ‖(N : K)‖ = 1) :
    ‖(n : K)‖ = 1 := by sorry
