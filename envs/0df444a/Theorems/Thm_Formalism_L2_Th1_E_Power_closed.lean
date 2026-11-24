-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Power_closed
-- name    : Formalism.L2.Th1.E.Power.closed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:22.765585+00:00
-- url     : https://prove2.me/theorems/4e7db709-6d73-46e9-9811-21369551fd72
-- title:
--   Power: closed
-- statement:
--   The Power construction uses the closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L45-L61

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

theorem Formalism.L2.Th1.E.Power.closed (g φ : ℕ → R) (e x : R) (k : ℕ) (h0 : g 0 = e * x) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → e ^ m * g (m + 1) * x ^ m =
      g 1 ^ (m + 1) * ∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j) := by sorry
