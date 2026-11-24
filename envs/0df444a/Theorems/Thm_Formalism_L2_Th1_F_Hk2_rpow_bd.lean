-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_rpow_bd
-- name    : Formalism.L2.Th1.F.Hk2.rpow_bd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:59.956867+00:00
-- url     : https://prove2.me/theorems/75fa6640-144c-44ee-a36c-5e9cdb0e3d48
-- title:
--   Hk2: rpow bd
-- statement:
--   The Hk2 construction uses the rpow bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L10-L14

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

theorem Formalism.L2.Th1.F.Hk2.rpow_bd {κ x t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hx : κ ≤ x) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    x ^ (-t) ≤ (κ ^ 2)⁻¹ := by sorry
