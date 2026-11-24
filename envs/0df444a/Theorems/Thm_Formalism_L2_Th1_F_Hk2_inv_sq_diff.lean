-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_inv_sq_diff
-- name    : Formalism.L2.Th1.F.Hk2.inv_sq_diff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:37.685711+00:00
-- url     : https://prove2.me/theorems/13e67b63-f443-4cb8-9286-6b176e3c675a
-- title:
--   Hk2: inv sq diff
-- statement:
--   The Hk2 construction uses the inv sq diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L38-L61

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

theorem Formalism.L2.Th1.F.Hk2.inv_sq_diff {ρ : ℝ} {w w' : ℂ} (hρ : 0 < ρ) (hw : ρ ≤ ‖w‖) (hw' : ρ ≤ ‖w'‖) :
    ‖(w ^ 2)⁻¹ - (w' ^ 2)⁻¹‖ ≤ 2 * (ρ ^ 3)⁻¹ * ‖w - w'‖ := by sorry
