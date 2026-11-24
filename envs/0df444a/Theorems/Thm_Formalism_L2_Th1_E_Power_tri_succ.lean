-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Power_tri_succ
-- name    : Formalism.L2.Th1.E.Power.tri_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:09.016659+00:00
-- url     : https://prove2.me/theorems/d83a18cf-73d0-4602-afc4-65f40365c697
-- title:
--   Power: tri succ
-- statement:
--   The Power construction uses the tri succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L15-L26

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
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
open Formalism.L2.Th1.E.Power
variable {R : Type} [CommRing R] [IsDomain R]

theorem Formalism.L2.Th1.E.Power.tri_succ (φ : ℕ → R) (m : ℕ) :
    ∏ j ∈ Finset.range (m + 1), φ (j + 1) ^ (m + 1 - j) =
      (∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j)) * ∏ j ∈ Finset.range (m + 1), φ (j + 1) := by sorry
