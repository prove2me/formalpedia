-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk1_norm_hk
-- name    : Formalism.L2.Th1.F.Hk1.norm_hk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:20.969802+00:00
-- url     : https://prove2.me/theorems/73341796-d8f6-4324-ad30-fd9f8b33e771
-- title:
--   Hk1: norm hk
-- statement:
--   The Hk1 construction uses the norm hk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelIntegralValue.lean#L13-L18

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue
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
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk1

theorem Formalism.L2.Th1.F.Hk1.norm_hk (s : ℝ) (w : ℂ) (hw : w ≠ 0) : ‖hk s w‖ = ‖w‖ ^ (-(2 + 2 * s)) := by sorry
