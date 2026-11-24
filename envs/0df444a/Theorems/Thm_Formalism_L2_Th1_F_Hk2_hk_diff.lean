-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_hk_diff
-- name    : Formalism.L2.Th1.F.Hk2.hk_diff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:31:01.667198+00:00
-- url     : https://prove2.me/theorems/af22fe7e-eb30-41a5-9f7c-bc59e330c8a3
-- title:
--   Hk2: hk diff
-- statement:
--   The Hk2 construction uses the hk diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L63-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L63-L96

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2

theorem Formalism.L2.Th1.F.Hk2.hk_diff {κ ρ s : ℝ} {w w' : ℂ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (hw : ρ ≤ ‖w‖)
    (hw' : ρ ≤ ‖w'‖) (hd : ‖w - w'‖ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖hk s w - hk s w'‖ ≤ 4 * (κ ^ 2)⁻¹ * (ρ ^ 3)⁻¹ := by sorry
