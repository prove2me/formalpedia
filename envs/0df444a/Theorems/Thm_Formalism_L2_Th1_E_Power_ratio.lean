-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Power_ratio
-- name    : Formalism.L2.Th1.E.Power.ratio
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:00.871602+00:00
-- url     : https://prove2.me/theorems/fcf8f656-c8a2-4fa1-9cfb-f5ce862505ff
-- title:
--   Power: ratio
-- statement:
--   The Power construction uses the ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L28-L43

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

theorem Formalism.L2.Th1.E.Power.ratio (g φ : ℕ → R) (k : ℕ) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → g (m + 1) * g 0 = (∏ j ∈ Finset.range m, φ (j + 1)) * g 1 * g m := by sorry
